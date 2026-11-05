'use strict';

/*
 * Alon Kozé — visioconférence P2P
 * =========
 *
 * ARCHITECTURE
 * - Chaque participant a son propre Peer avec un ID aléatoire (« moi »).
 * - Chacun est relié directement à tous les autres par un appel WebRTC (maillage / mesh).
 * - L'ID du salon sert uniquement d'ANNUAIRE : un participant le réserve et donne
 *   aux nouveaux arrivants la liste des présents ; ils appellent alors chacun d'eux.
 *   Si le détenteur part, un autre reprend l'annuaire. Aucun flux n'y transite.
 * - Chaque paire a aussi un petit canal de données (« lien ») : authentification,
 *   prénom, et taille d'affichage (pour n'envoyer que la qualité utile).
 *
 * SÉCURITÉ
 * - La clé passe par PBKDF2 (600 000 itérations) puis HKDF, et donne deux valeurs
 *   indépendantes (détails dans deriverCles) :
 *     · l'ID du salon, public (le serveur de signalisation le voit) ;
 *     · une clé d'authentification HMAC, qui ne quitte jamais l'appareil.
 * - Toute connexion (annuaire ou participant) commence par une authentification
 *   mutuelle : chacun signe avec la clé HMAC les défis (nonces) des deux côtés ET les
 *   empreintes DTLS des connexions WebRTC concernées. Un intermédiaire — y compris
 *   un serveur de signalisation malveillant — aurait des empreintes différentes de
 *   chaque côté : sa preuve, ou celle qu'il relaie, ne correspondrait pas.
 * - Tant qu'un participant n'est pas vérifié, on ne lui envoie ni son ni image
 *   (pistes remplacées par « rien ») et on n'affiche pas ce qu'il envoie.
 * - Les prénoms ne circulent que dans les canaux authentifiés : le serveur de
 *   signalisation ne voit que des identifiants aléatoires.
 */

const PEER_OPTS = {
    config: {
        iceServers: [
            { urls: 'stun:stun.l.google.com:19302' },
            { urls: 'stun:stun.cloudflare.com:3478' }
        ]
    }
};
const MAX_PARTICIPANTS = 8;
const ITERATIONS_PBKDF2 = 600000;
const DELAI_AUTH = 20000;

const $ = id => document.getElementById(id);

let localStream = null;
let moi = null;               // mon Peer (ID aléatoire)
let annuaire = null;          // Peer(roomId) si c'est moi qui tiens l'annuaire
let membres = new Map();      // (annuaire) id -> { nom, conn }
let connAnnuaire = null;      // mon lien vers l'annuaire (si je ne le tiens pas)
const appels = new Map();     // id -> { call, initiateur, nom, stream, callVerifie, tuile, video, label }
const liens = new Map();      // id -> { conn, poignee, fini }
const vues = new Map();       // id -> { h, visible } : comment ce participant m'affiche
const vuesEnvoyees = new Map(); // id -> dernière vue que je lui ai envoyée
let roomId = null;
let cleAuth = null;           // CryptoKey HMAC (non exportable)
let monNom = '';
let quitte = true;
let timerAnnuaire = null;
let timerMoi = null;
let screenTrack = null;
let sansCamera = false;

try { $('pseudo').value = localStorage.getItem('visio-pseudo') || ''; } catch {}

const nettoyerNom = n => (typeof n === 'string' && n.trim() ? n.trim().slice(0, 30) : 'Anonyme');

/* =====================================================================
 * Cryptographie
 * ===================================================================== */

const te = new TextEncoder();
const hex = b => Array.from(b, x => x.toString(16).padStart(2, '0')).join('');
const deHex = s => new Uint8Array((s.match(/../g) || []).map(h => parseInt(h, 16)));
const aleatoire = (n = 16) => hex(crypto.getRandomValues(new Uint8Array(n)));

/*
 * clé tapée ──PBKDF2 (600 000 itérations, partie lente)──► secret maître (32 octets)
 *     secret maître ──HKDF « identifiant-salon » ──► ID du salon (16 octets, public)
 *     secret maître ──HKDF « authentification »  ──► clé HMAC (32 octets, secrète)
 *
 * - Un seul bloc PBKDF2 : le coût lent n'est payé qu'une fois. (Demander 64 octets
 *   à PBKDF2 calculait deux blocs, soit le double de travail pour nous, alors
 *   qu'un attaquant n'a besoin que d'un bloc pour tester une clé.)
 * - HKDF est fait pour tirer plusieurs clés d'un même secret : grâce aux libellés
 *   différents, l'ID public ne révèle rien de la clé HMAC.
 * - La clé HMAC est produite directement par le navigateur (deriveKey), non
 *   exportable : ses octets ne passent jamais par le JavaScript.
 */
async function deriverCles(cle) {
    const base = await crypto.subtle.importKey('raw', te.encode(cle.normalize('NFC')), 'PBKDF2', false, ['deriveBits']);
    const maitre = new Uint8Array(await crypto.subtle.deriveBits(
        { name: 'PBKDF2', hash: 'SHA-256', salt: te.encode('visio-p2p/salon/v3'), iterations: ITERATIONS_PBKDF2 },
        base, 256));
    const hkdf = await crypto.subtle.importKey('raw', maitre, 'HKDF', false, ['deriveBits', 'deriveKey']);
    maitre.fill(0); // le navigateur en a gardé sa copie, inutile de laisser traîner celle-ci

    const etiquette = info => ({ name: 'HKDF', hash: 'SHA-256', salt: new Uint8Array(32), info: te.encode('visio-p2p/v3/' + info) });
    const idBits = new Uint8Array(await crypto.subtle.deriveBits(etiquette('identifiant-salon'), hkdf, 128));
    const cleHmac = await crypto.subtle.deriveKey(etiquette('authentification'), hkdf,
        { name: 'HMAC', hash: 'SHA-256', length: 256 }, false, ['sign', 'verify']);

    return { roomId: 'visio-' + hex(idBits), cleAuth: cleHmac };
}

const messageSigne = parts => te.encode(['visio-auth-v1', ...parts].join('|'));

async function signer(parts) {
    return hex(new Uint8Array(await crypto.subtle.sign('HMAC', cleAuth, messageSigne(parts))));
}

async function verifierSignature(sig, parts) {
    if (typeof sig !== 'string' || !/^[0-9a-f]{64}$/.test(sig)) return false;
    return crypto.subtle.verify('HMAC', cleAuth, deHex(sig), messageSigne(parts));
}

// Empreintes des certificats DTLS annoncées dans une description SDP
function empreintesSdp(sdp) {
    const lignes = (sdp || '').match(/^a=fingerprint:.+$/gm) || [];
    return [...new Set(lignes.map(l => l.slice(14).trim().toLowerCase()))].sort().join(',');
}

// { local, distant } pour une liste de connexions WebRTC, ou null si pas encore prêtes
function empreintes(pcs) {
    const local = [], distant = [];
    for (const pc of pcs) {
        if (!pc || !pc.localDescription || !pc.remoteDescription) return null;
        const a = empreintesSdp(pc.localDescription.sdp);
        const b = empreintesSdp(pc.remoteDescription.sdp);
        if (!a || !b) return null;
        local.push(a);
        distant.push(b);
    }
    return { local: local.join(';'), distant: distant.join(';') };
}

/*
 * Authentification mutuelle sur un canal de données.
 *   1. chacun envoie un défi aléatoire (nonce) ;
 *   2. chacun envoie preuve = HMAC(clé, contexte | son rôle | rôle de l'autre |
 *      son nonce | nonce de l'autre | ses empreintes DTLS | empreintes vues chez l'autre) ;
 *   3. chacun vérifie la preuve de l'autre avec SES propres valeurs.
 * Les rôles et l'ordre des nonces empêchent de renvoyer à quelqu'un sa propre preuve.
 * Les empreintes peuvent changer (appel remplacé) : la preuve est alors refaite.
 * Les autres messages ne sont transmis à `onMessage` qu'une fois l'autre vérifié.
 */
//
// Robustesse : un message envoyé juste à l'ouverture d'un canal PeerJS peut se
// perdre. Le défi est donc répété tant que l'autre n'est pas vérifié, la preuve
// est renvoyée à chaque défi reçu, et elle contient aussi le nonce de l'émetteur.
function poignee(conn, { contexte, moiRole, autreRole, pcs, onVerifie, onMessage, onEchec }) {
    const st = {
        ok: false, preuveInvalide: false,
        monNonce: aleatoire(), leurNonce: null, leurPreuve: null,
        envoye: null, dernierePreuve: null, verifie: null, tampon: []
    };
    const nonceValide = n => typeof n === 'string' && /^[0-9a-f]{32}$/.test(n);
    const envoyerPreuve = () => {
        if (st.dernierePreuve) try { conn.send({ type: 'preuve', nonce: st.monNonce, preuve: st.dernierePreuve }); } catch {}
    };

    st.relancer = async () => {
        if (!st.leurNonce || !conn.open) return;
        const liste = pcs();
        const fp = empreintes(liste);
        if (!fp) return; // connexions pas encore négociées : on sera relancé
        const cleFp = fp.local + '/' + fp.distant;

        if (st.envoye !== cleFp) {
            st.envoye = cleFp;
            st.dernierePreuve = await signer([contexte, moiRole, autreRole, st.monNonce, st.leurNonce, fp.local, fp.distant]);
            envoyerPreuve();
        }

        const preuve = st.leurPreuve;
        if (!preuve || st.verifie === cleFp + preuve) return;
        const ok = await verifierSignature(preuve, [contexte, autreRole, moiRole, st.leurNonce, st.monNonce, fp.distant, fp.local]);
        if (!ok) { st.preuveInvalide = true; return; } // on attend une autre preuve, ou le délai
        st.verifie = cleFp + preuve;
        st.preuveInvalide = false;
        const premiereFois = !st.ok;
        st.ok = true;
        onVerifie(liste);
        if (premiereFois) {
            const t = st.tampon;
            st.tampon = [];
            t.forEach(onMessage);
        }
    };

    const envoyerDefi = () => { try { conn.send({ type: 'defi', nonce: st.monNonce }); } catch {} };
    if (conn.open) envoyerDefi(); else conn.on('open', envoyerDefi);

    // Répétition du défi tant que l'autre n'est pas vérifié
    const repetition = setInterval(() => {
        if (st.ok || st.fini) return clearInterval(repetition);
        if (conn.open) envoyerDefi();
        st.relancer();
    }, 2000);
    conn.on('close', () => { st.fini = true; });

    conn.on('data', msg => {
        if (!msg || typeof msg !== 'object') return;
        if (msg.type === 'defi') {
            if (!st.leurNonce && nonceValide(msg.nonce)) st.leurNonce = msg.nonce;
            envoyerPreuve(); // l'autre n'a peut-être pas reçu ma preuve
            st.relancer();
        } else if (msg.type === 'preuve') {
            if (!st.leurNonce && nonceValide(msg.nonce)) st.leurNonce = msg.nonce;
            if (typeof msg.preuve === 'string') st.leurPreuve = msg.preuve;
            st.relancer();
        } else if (st.ok) {
            onMessage(msg);
        } else if (st.tampon.length < 20) {
            st.tampon.push(msg);
        }
    });

    setTimeout(() => { if (!st.ok) { clearInterval(repetition); onEchec(st); } }, DELAI_AUTH);
    return st;
}

/* =====================================================================
 * Clé : force et génération
 * ===================================================================== */

function forceCle(cle) {
    if (!cle) return { niveau: '', texte: '' };
    let alphabet = 0;
    if (/[a-z]/.test(cle)) alphabet += 26;
    if (/[A-Z]/.test(cle)) alphabet += 26;
    if (/[0-9]/.test(cle)) alphabet += 10;
    if (/[^a-zA-Z0-9]/.test(cle)) alphabet += 20;
    let bits = cle.length * Math.log2(Math.max(alphabet, 2));
    // Peu de caractères différents (« aaaa1111 ») : estimation bien plus basse
    bits = Math.min(bits, new Set(cle).size * 5);
    if (bits < 45) return { niveau: 'faible', texte: '⚠️ Clé faible : facile à deviner. Utilise « Générer » ou une phrase de 4 mots ou plus.' };
    if (bits < 70) return { niveau: 'moyenne', texte: 'Clé moyenne. Une clé plus longue serait plus sûre.' };
    return { niveau: 'forte', texte: '✓ Clé forte' };
}

function majForce() {
    const f = forceCle($('secretKey').value);
    $('force').className = f.niveau;
    $('force').textContent = f.texte;
}

// 20 caractères tirés au hasard parmi 31 (sans 0/o, 1/l/i) : environ 99 bits
function genererCle() {
    const A = 'abcdefghjkmnpqrstuvwxyz23456789';
    let s = '';
    while (s.replace(/-/g, '').length < 20) {
        const b = crypto.getRandomValues(new Uint8Array(1))[0];
        if (b >= 248) continue; // 248 = 8 × 31 : évite de favoriser certains caractères
        if (s.length && s.replace(/-/g, '').length % 4 === 0) s += '-';
        s += A[b % 31];
    }
    return s;
}

/* =====================================================================
 * Médias locaux
 * ===================================================================== */

async function getMedia() {
    sansCamera = false;
    try {
        return await navigator.mediaDevices.getUserMedia({ video: true, audio: true });
    } catch (e) {
        // Pas de caméra (ou refusée) : audio seul + piste vidéo noire,
        // pour qu'il existe toujours un canal vidéo (utile au partage d'écran)
        const s = await navigator.mediaDevices.getUserMedia({ audio: true });
        s.addTrack(pisteNoire());
        sansCamera = true;
        return s;
    }
}

function pisteNoire() {
    const c = Object.assign(document.createElement('canvas'), { width: 640, height: 480 });
    c.getContext('2d').fillRect(0, 0, c.width, c.height);
    return c.captureStream(1).getVideoTracks()[0];
}

const cameraTrack = () => localStream && localStream.getVideoTracks()[0];

// Émetteur audio ou vidéo d'une connexion (y compris quand sa piste est coupée)
function emetteur(pc, kind) {
    const t = pc && pc.getTransceivers().find(t => t.receiver.track && t.receiver.track.kind === kind);
    return t && t.sender;
}

// Rien n'est envoyé à un participant tant qu'il n'est pas vérifié
function couperEnvoi(call) {
    const pc = call.peerConnection;
    if (pc) pc.getSenders().forEach(s => s.replaceTrack(null).catch(() => {}));
}

function ouvrirEnvoi(call) {
    const pc = call.peerConnection;
    const a = emetteur(pc, 'audio');
    const v = emetteur(pc, 'video');
    if (a) a.replaceTrack(localStream.getAudioTracks()[0] || null).catch(e => console.error(e));
    if (v) v.replaceTrack(screenTrack || cameraTrack() || null).catch(e => console.error(e));
}

/* =====================================================================
 * Statut
 * ===================================================================== */

let alerte = '';
let timerAlerte = null;
let debitTexte = '';

function setStatus(txt) {
    $('status').textContent = alerte || txt;
    $('status').classList.toggle('alerte', !!alerte);
}

function signaler(msg) {
    alerte = msg;
    clearTimeout(timerAlerte);
    timerAlerte = setTimeout(() => { alerte = ''; majStatut(); }, 10000);
    majStatut();
}

function majStatut() {
    if (quitte) return;
    const verifies = [...appels.values()].filter(e => e.callVerifie === e.call && e.stream).length;
    const enCours = appels.size - verifies;
    if (verifies === 0 && enCours === 0) setStatus('Dans le salon. En attente d\'autres participants…');
    else setStatus(`${verifies + 1} participant${verifies ? 's' : ''} · vérifiés 🔒`
        + (enCours ? ` · ${enCours} en vérification…` : '')
        + (debitTexte ? ` · ${debitTexte}` : ''));
}

// Débit réellement envoyé (toutes connexions confondues), mesuré toutes les 2 s
let mesurePrecedente = null;
setInterval(async () => {
    if (quitte || !appels.size) { debitTexte = ''; mesurePrecedente = null; return; }
    let octets = 0;
    for (const e of appels.values()) {
        const pc = e.call.peerConnection;
        if (!pc) continue;
        try {
            (await pc.getStats()).forEach(r => { if (r.type === 'outbound-rtp') octets += r.bytesSent || 0; });
        } catch {}
    }
    const t = performance.now();
    if (mesurePrecedente && octets >= mesurePrecedente.octets) {
        const mbps = (octets - mesurePrecedente.octets) * 8 / (t - mesurePrecedente.t) / 1000;
        debitTexte = `↑ ${mbps.toFixed(mbps < 1 ? 2 : 1)} Mb/s`;
    }
    mesurePrecedente = { octets, t };
    majStatut();
}, 2000);

/* =====================================================================
 * Entrée dans le salon
 * ===================================================================== */

async function rejoindre() {
    const cle = $('secretKey').value;
    if (!cle) return alert('Entre une clé secrète !');
    if (forceCle(cle).niveau === 'faible'
        && !confirm('Cette clé est facile à deviner : quelqu\'un pourrait entrer dans le salon. Continuer quand même ?')) return;
    monNom = nettoyerNom($('pseudo').value);
    try { localStorage.setItem('visio-pseudo', $('pseudo').value.trim()); } catch {}

    $('btnJoin').disabled = true;
    $('setup').hidden = true;
    $('call').hidden = false;
    $('localLabel').textContent = monNom + ' (moi)';

    try {
        localStream = await getMedia();
    } catch (e) {
        console.error(e);
        $('btnJoin').disabled = false;
        setStatus("Impossible d'accéder au micro / à la caméra (la page doit être en HTTPS).");
        return;
    }
    $('localVideo').srcObject = localStream;
    majBoutons();

    setStatus('Préparation de la clé…');
    ({ roomId, cleAuth } = await deriverCles(cle));
    $('secretKey').value = ''; // la clé en clair n'est plus nécessaire
    majForce();
    $('btnJoin').disabled = false;
    quitte = false;
    creerMoi();
}

function creerMoi() {
    if (quitte) return;
    setStatus('Connexion au serveur de signalisation…');
    const p = new Peer(PEER_OPTS);
    moi = p;

    p.on('open', () => {
        if (moi !== p) return;
        majStatut();
        rejoindreAnnuaire();
    });
    p.on('call', recevoirAppel);
    p.on('connection', brancherLien);
    p.on('disconnected', () => {
        // Perte du serveur de signalisation : les appels en cours continuent,
        // on se reconnecte simplement pour pouvoir accueillir de nouveaux venus.
        if (moi !== p || p.destroyed || quitte) return;
        clearTimeout(timerMoi);
        timerMoi = setTimeout(() => { if (moi === p && !p.destroyed && p.disconnected) p.reconnect(); }, 2000);
    });
    p.on('error', err => erreurMoi(p, err));
}

function erreurMoi(p, err) {
    if (moi !== p || quitte) return;
    console.warn('Peer :', err.type, err.message);
    if (err.type === 'peer-unavailable') {
        const id = (String(err.message).match(/peer (\S+)$/) || [])[1];
        if (id === roomId) {
            // Annuaire introuvable (son détenteur vient de partir) : on retente
            if (connAnnuaire) { const c = connAnnuaire; connAnnuaire = null; c.close(); }
            planifierAnnuaire();
        } else if (id && appels.has(id)) {
            retirer(id);
        }
    } else if (['network', 'server-error', 'socket-error', 'socket-closed'].includes(err.type)) {
        setStatus('Serveur de signalisation injoignable, nouvel essai…');
        clearTimeout(timerMoi);
        timerMoi = setTimeout(() => {
            if (moi !== p || quitte) return;
            if (p.destroyed) creerMoi();
            else if (p.disconnected) p.reconnect();
        }, 3000);
    } else {
        setStatus('Erreur : ' + err.type);
    }
}

/* =====================================================================
 * Annuaire
 * ===================================================================== */

function planifierAnnuaire(delai = 500 + Math.random() * 2000) {
    clearTimeout(timerAnnuaire);
    timerAnnuaire = setTimeout(rejoindreAnnuaire, delai);
}

// Tente de tenir l'annuaire ; s'il est déjà tenu, s'y connecte comme simple membre.
function rejoindreAnnuaire() {
    if (quitte || annuaire || connAnnuaire) return;
    if (!moi || !moi.open) return planifierAnnuaire(2000);

    const a = new Peer(roomId, PEER_OPTS);

    a.on('open', () => {
        if (quitte) return a.destroy();
        annuaire = a;
        // Je connais déjà les participants vérifiés avec qui je suis en appel
        membres = new Map([[moi.id, { nom: monNom, conn: null }]]);
        for (const [id, e] of appels) if (e.callVerifie === e.call) membres.set(id, { nom: e.nom, conn: null });
        console.log('Je tiens l\'annuaire du salon');
        // Rediffusion régulière de la liste : rattrape un message perdu ou un lien
        // entre deux participants qui aurait échoué
        const diffusion = setInterval(() => {
            if (annuaire !== a || a.destroyed) return clearInterval(diffusion);
            for (const m of membres.values()) if (m.conn && m.conn.open) envoyerListe(m.conn);
        }, 15000);
    });

    a.on('connection', accueillir);

    a.on('disconnected', () => {
        if (annuaire === a && !a.destroyed && !quitte) setTimeout(() => { if (!a.destroyed && a.disconnected) a.reconnect(); }, 2000);
    });

    a.on('error', err => {
        const etaitAnnuaire = annuaire === a;
        a.destroy();
        if (etaitAnnuaire) annuaire = null;
        if (quitte) return;
        if (err.type === 'unavailable-id') {
            seConnecterAnnuaire(); // quelqu'un d'autre le tient déjà
        } else {
            console.warn('Annuaire :', err.type);
            planifierAnnuaire(3000);
        }
    });
}

// (côté annuaire) Un participant se présente. Il n'obtient la liste des présents
// qu'après avoir prouvé qu'il connaît la clé.
function accueillir(conn) {
    if (quitte) return conn.close();
    poignee(conn, {
        contexte: 'annuaire', moiRole: 'annuaire', autreRole: conn.peer,
        pcs: () => [conn.peerConnection],
        onVerifie: () => {},
        onMessage: msg => {
            if (msg.type !== 'bonjour') return;
            // Déjà inscrit : la liste s'est sans doute perdue, on la renvoie
            if ((membres.get(conn.peer) || {}).conn === conn) return envoyerListe(conn);
            if (!membres.has(conn.peer) && membres.size >= MAX_PARTICIPANTS) {
                conn.send({ type: 'plein' });
                setTimeout(() => conn.close(), 1000);
                return;
            }
            envoyerListe(conn);
            membres.set(conn.peer, { nom: nettoyerNom(msg.nom), conn });
        },
        onEchec: () => { console.warn('Annuaire : connexion non authentifiée refusée'); conn.close(); }
    });
    surveillerFin(conn, () => {
        const m = membres.get(conn.peer);
        if (m && m.conn === conn) membres.delete(conn.peer);
    });
}

function envoyerListe(conn) {
    const liste = [...membres]
        .filter(([id]) => id !== conn.peer)
        .map(([id, m]) => ({ id, nom: m.nom }));
    conn.send({ type: 'liste', membres: liste });
}

// (côté membre) Connexion à l'annuaire tenu par quelqu'un d'autre. On vérifie
// aussi l'annuaire : un faux annuaire ne peut ni nous envoyer de liste, ni « plein ».
function seConnecterAnnuaire() {
    if (quitte || !moi || !moi.open) return planifierAnnuaire(2000);
    const conn = moi.connect(roomId, { reliable: true });
    connAnnuaire = conn;
    let bonjourEnvoye = false;
    let listeRecue = false;

    const abandonner = () => {
        if (connAnnuaire !== conn || listeRecue) return;
        connAnnuaire = null;
        conn.close();
        planifierAnnuaire();
    };
    let delai = setTimeout(abandonner, 10000);
    conn.on('open', () => { clearTimeout(delai); delai = setTimeout(abandonner, DELAI_AUTH + 2000); });

    poignee(conn, {
        contexte: 'annuaire', moiRole: moi.id, autreRole: 'annuaire',
        pcs: () => [conn.peerConnection],
        onVerifie: () => {
            if (bonjourEnvoye) return;
            bonjourEnvoye = true;
            // « bonjour » répété tant que la liste n'est pas arrivée (message perdu)
            const envoyer = () => {
                if (listeRecue || connAnnuaire !== conn || !conn.open) return clearInterval(rep);
                try { conn.send({ type: 'bonjour', nom: monNom }); } catch {}
            };
            const rep = setInterval(envoyer, 3000);
            envoyer();
        },
        onMessage: msg => {
            if (msg.type === 'liste' && Array.isArray(msg.membres)) {
                listeRecue = true;
                clearTimeout(delai);
                // J'appelle tous ceux avec qui je ne suis pas encore connecté
                msg.membres.slice(0, MAX_PARTICIPANTS).forEach(m => {
                    if (m && typeof m.id === 'string' && m.id.length < 100) appeler(m.id, nettoyerNom(m.nom));
                });
                majStatut();
            } else if (msg.type === 'plein' && appels.size === 0) {
                quitte = true; // on n'insiste pas
                setStatus(`Salon plein (${MAX_PARTICIPANTS} personnes maximum).`);
            }
        },
        onEchec: st => {
            if (connAnnuaire !== conn) return;
            if (st.preuveInvalide) signaler('⚠️ L\'annuaire du salon est tenu par quelqu\'un qui n\'a pas la bonne clé. Nouvel essai…');
            abandonner();
        }
    });

    surveillerFin(conn, () => {
        clearTimeout(delai);
        if (connAnnuaire !== conn) return;
        connAnnuaire = null;
        planifierAnnuaire(); // le détenteur est parti : quelqu'un doit reprendre l'annuaire
    });
}

/* =====================================================================
 * Appels (un par participant)
 * ===================================================================== */

function appeler(id, nom) {
    if (quitte || !moi || id === moi.id || appels.has(id)) return;
    const call = moi.call(id, localStream);
    if (!call) return;
    couperEnvoi(call);
    brancher(call, id, nom, moi.id);
}

function recevoirAppel(call) {
    const id = call.peer;
    const initiateur = id;
    // Deux participants peuvent s'appeler mutuellement au même moment : on garde
    // l'appel lancé par le plus petit ID (règle appliquée identiquement des deux côtés).
    const existant = appels.get(id);
    if (quitte || (existant && initiateur > existant.initiateur)) { call.close(); return; }
    if (!existant && appels.size >= MAX_PARTICIPANTS - 1) { call.close(); return; }
    call.answer(localStream);
    couperEnvoi(call); // rien ne part avant la vérification
    brancher(call, id, existant ? existant.nom : '…', initiateur);
}

function brancher(call, id, nom, initiateur) {
    let e = appels.get(id);
    if (e) {
        // Remplacement d'un appel en doublon : on garde la tuile, mais il faut revérifier
        const ancien = e.call;
        e.call = call;
        e.initiateur = initiateur;
        e.stream = null;
        e.video.srcObject = null;
        e.tuile.classList.add('attente');
        ancien.close();
    } else {
        e = { call, initiateur, nom, stream: null, callVerifie: null, ...creerTuile(id, nom) };
        appels.set(id, e);
    }

    const relancer = () => { const l = liens.get(id); if (l) l.poignee.relancer(); };

    call.on('stream', stream => {
        if (e.call !== call) return;
        e.stream = stream;
        if (e.callVerifie === call) afficherFlux(e);
        relancer();
    });
    if (call.peerConnection) call.peerConnection.addEventListener('signalingstatechange', relancer);

    // Pas vérifié à temps : on raccroche (mauvaise clé, pare-feu strict, participant parti…)
    const delai = setTimeout(() => { if (e.call === call && e.callVerifie !== call) refuser(id); }, DELAI_AUTH + 5000);

    surveillerFin(call, () => {
        clearTimeout(delai);
        if (appels.get(id) && appels.get(id).call === call) retirer(id);
    });

    // Le lien de données est ouvert par le participant au plus petit ID
    if (moi.id < id) ouvrirLien(id); else relancer();
    majStatut();
}

// Appelé quand l'autre a prouvé connaître la clé, empreintes de CET appel comprises
function authentifie(id, pcVerifie) {
    const e = appels.get(id);
    if (!e || e.call.peerConnection !== pcVerifie || e.callVerifie === e.call) return;
    e.callVerifie = e.call;
    ouvrirEnvoi(e.call);
    if (e.stream) afficherFlux(e);
    appliquerQualite();
    majStatut();
    planifierVues();
}

function afficherFlux(e) {
    e.video.srcObject = e.stream;
    e.tuile.classList.remove('attente');
    majStatut();
}

function refuser(id) {
    const l = liens.get(id);
    if (l && l.poignee.preuveInvalide) signaler('⚠️ Un participant n\'avait pas la bonne clé : il a été déconnecté.');
    retirer(id);
}

function retirer(id) {
    const e = appels.get(id);
    if (!e) return;
    appels.delete(id);
    if (e.tuile.classList.contains('pin')) epingler(null);
    observateur.unobserve(e.video);
    e.tuile.remove();
    e.call.close();
    const l = liens.get(id);
    liens.delete(id);
    if (l) l.conn.close();
    vues.delete(id);
    vuesEnvoyees.delete(id);
    // (annuaire) un membre connu seulement par l'appel est considéré comme parti
    const m = membres.get(id);
    if (annuaire && m && !m.conn) membres.delete(id);
    appliquerQualite(); // le budget se répartit entre les participants restants
    majGrille();
    majStatut();
}

// Appelle `cb` une seule fois quand la connexion (appel ou données) est terminée.
// L'événement 'close' de PeerJS n'est pas fiable si l'autre ferme brutalement son
// onglet : on surveille aussi directement l'état de la connexion WebRTC.
function surveillerFin(obj, cb) {
    let fait = false, t = null;
    const fin = () => { if (fait) return; fait = true; clearTimeout(t); cb(); };
    obj.on('close', fin);
    obj.on('error', fin);
    const pc = obj.peerConnection;
    if (pc) {
        pc.addEventListener('iceconnectionstatechange', () => {
            const s = pc.iceConnectionState;
            clearTimeout(t);
            if (s === 'failed' || s === 'closed') fin();
            else if (s === 'disconnected') t = setTimeout(fin, 5000);
        });
    }
}

/* =====================================================================
 * Liens directs : authentification, prénom, taille d'affichage
 * ===================================================================== */

function ouvrirLien(id) {
    if (quitte || !moi) return;
    const l = liens.get(id);
    if (l && !l.fini) { l.poignee.relancer(); return; }
    brancherLien(moi.connect(id, { reliable: true }));
}

function brancherLien(conn) {
    const id = conn.peer;
    if (quitte || (!appels.has(id) && liens.size >= MAX_PARTICIPANTS * 2)) { conn.close(); return; }
    const ancien = liens.get(id);
    const l = { conn, fini: false, nomEnvoye: false, nomRecu: false };
    liens.set(id, l);
    if (ancien) ancien.conn.close();
    const envoyerNom = () => { try { conn.send({ type: 'nom', nom: monNom }); } catch {} };

    l.poignee = poignee(conn, {
        contexte: 'pair', moiRole: moi.id, autreRole: id,
        // On authentifie à la fois l'appel (son et image) et ce lien lui-même
        pcs: () => { const e = appels.get(id); return [e && e.call.peerConnection, conn.peerConnection]; },
        onVerifie: pcsVerifies => {
            if (!l.nomEnvoye) {
                l.nomEnvoye = true;
                envoyerNom();
                // Le prénom peut se perdre : on le redemande tant qu'on ne l'a pas reçu
                let essais = 0;
                const rep = setInterval(() => {
                    if (l.nomRecu || l.fini || ++essais > 5) return clearInterval(rep);
                    try { conn.send({ type: 'demandeNom' }); } catch {}
                }, 3000);
            }
            vuesEnvoyees.delete(id);
            authentifie(id, pcsVerifies[0]);
        },
        onMessage: msg => {
            if (msg.type === 'vue') recevoirVue(id, msg);
            else if (msg.type === 'demandeNom') envoyerNom();
            else if (msg.type === 'nom') {
                l.nomRecu = true;
                const e = appels.get(id);
                if (e) { e.nom = nettoyerNom(msg.nom); e.label.textContent = e.nom; }
            }
        },
        onEchec: () => { if (liens.get(id) === l) refuser(id); }
    });

    surveillerFin(conn, () => {
        l.fini = true;
        if (liens.get(id) !== l) return;
        liens.delete(id);
        // Lien perdu alors que l'appel continue : on le rouvre (si c'est à moi de le faire)
        if (appels.has(id) && moi && moi.id < id) setTimeout(() => ouvrirLien(id), 2000);
    });
}

const PALIERS = [120, 180, 240, 360, 480, 540, 720, 1080, 1440, 2160];

function recevoirVue(id, msg) {
    if (typeof msg.h !== 'number' || !isFinite(msg.h)) return;
    vues.set(id, { h: Math.min(2160, Math.max(90, msg.h)), visible: msg.visible !== false });
    appliquerQualite();
}

// Hauteur (en pixels physiques) à laquelle j'affiche la vidéo de ce participant
function mesurerVue(e) {
    const v = e.video;
    const visible = document.visibilityState === 'visible'
                 && e.tuile.getClientRects().length > 0 && v.clientHeight > 0;
    let h = v.clientHeight;
    // object-fit: contain → l'image n'occupe pas forcément toute la hauteur
    if (v.videoWidth && v.videoHeight && v.clientWidth) h = Math.min(h, v.clientWidth * v.videoHeight / v.videoWidth);
    h = Math.round(h * (window.devicePixelRatio || 1));
    const palier = PALIERS.find(p => p >= h) || PALIERS[PALIERS.length - 1];
    return { type: 'vue', h: palier, visible };
}

let timerVues = null;
function planifierVues() {
    clearTimeout(timerVues);
    timerVues = setTimeout(envoyerVues, 250);
}

function envoyerVues() {
    for (const [id, e] of appels) {
        const l = liens.get(id);
        if (!l || !l.conn.open || !l.poignee.ok) continue;
        const vue = mesurerVue(e);
        const cle = vue.h + '/' + vue.visible;
        if (vuesEnvoyees.get(id) === cle) continue;
        vuesEnvoyees.set(id, cle);
        try { l.conn.send(vue); } catch (err) { console.warn(err); }
    }
}

// Toute variation de taille d'une tuile (fenêtre, grille, plein écran, épinglage…)
const observateur = new ResizeObserver(planifierVues);
document.addEventListener('visibilitychange', planifierVues);
// Renvoi périodique, au cas où un message se serait perdu
setInterval(() => { vuesEnvoyees.clear(); planifierVues(); }, 10000);

/* =====================================================================
 * Tuiles vidéo
 * ===================================================================== */

function creerTuile(id, nom) {
    const tuile = document.createElement('div');
    tuile.className = 'tile distant attente';
    tuile.title = 'Double-clic : agrandir';
    const video = document.createElement('video');
    video.autoplay = true;
    video.playsInline = true;
    const label = document.createElement('span');
    label.textContent = nom; // textContent : le nom vient d'un tiers, jamais en HTML
    tuile.append(video, label);
    tuile.addEventListener('dblclick', () => {
        const focus = $('call').classList.contains('focus');
        if (!focus) { pleinEcran(true); epingler(tuile); }
        else epingler(tuile.classList.contains('pin') ? null : tuile);
    });
    $('grille').appendChild(tuile);
    observateur.observe(video);
    video.addEventListener('resize', planifierVues); // résolution reçue modifiée
    majGrille();
    return { tuile, video, label };
}

// Une seule tuile affichée en grand (null = retour à la grille)
function epingler(tuile) {
    document.querySelectorAll('.distant.pin').forEach(t => t.classList.remove('pin'));
    if (tuile) tuile.classList.add('pin');
    $('grille').classList.toggle('epingle', !!tuile);
    majGrille();
}

// En plein écran : grille la plus carrée possible selon le nombre de participants
function majGrille() {
    const n = $('grille').classList.contains('epingle') ? 1 : Math.max(1, appels.size);
    const cols = Math.ceil(Math.sqrt(n));
    $('grille').style.setProperty('--cols', cols);
    $('grille').style.setProperty('--rows', Math.ceil(n / cols));
    planifierVues();
}

/* =====================================================================
 * Partage d'écran & qualité
 * ===================================================================== */

// Émetteurs vidéo vers les participants VÉRIFIÉS uniquement
function sendersVideo() {
    const liste = [];
    for (const [id, e] of appels) {
        if (e.callVerifie !== e.call) continue;
        const sender = emetteur(e.call.peerConnection, 'video');
        if (sender) liste.push({ id, sender });
    }
    return liste;
}

// Remplace la piste vidéo envoyée à tous les participants, sans renégocier
async function envoyerVideo(track) {
    if (track) await Promise.all(sendersVideo().map(({ sender }) => sender.replaceTrack(track).catch(e => console.error(e))));
    appliquerQualite();
}

/*
 * contraintes : ce que la caméra / la capture d'écran produit (résolution, fps)
 * encodage    : plafond pour UN participant qui m'affiche en grand
 *               (débit max, fps max, réduction de résolution)
 * budget      : plafond d'envoi TOTAL, partagé entre tous les participants
 * hint        : sacrifier la fluidité ('detail') ou la netteté ('motion')
 */
const QUALITE_CAM = {
    auto:    { budget: 4000000, contraintes: {}, encodage: { maxBitrate: 2500000 } },
    basse:   { budget: 750000,  contraintes: { width: { ideal: 320 },  height: { ideal: 240 },  frameRate: { ideal: 15 } }, encodage: { maxBitrate: 250000,  maxFramerate: 15 } },
    moyenne: { budget: 2000000, contraintes: { width: { ideal: 640 },  height: { ideal: 480 },  frameRate: { ideal: 24 } }, encodage: { maxBitrate: 800000,  maxFramerate: 24 } },
    haute:   { budget: 5000000, contraintes: { width: { ideal: 1280 }, height: { ideal: 720 },  frameRate: { ideal: 30 } }, encodage: { maxBitrate: 2500000, maxFramerate: 30 } },
    hd:      { budget: 8000000, contraintes: { width: { ideal: 1920 }, height: { ideal: 1080 }, frameRate: { ideal: 30 } }, encodage: { maxBitrate: 4500000, maxFramerate: 30 } }
};

const QUALITE_ECRAN = {
    texte:     { budget: 5000000, hint: 'detail', contraintes: { frameRate: { ideal: 5,  max: 5 } },  encodage: { maxBitrate: 2500000, maxFramerate: 5 } },
    equilibre: { budget: 4000000, hint: 'detail', contraintes: { frameRate: { ideal: 15, max: 15 } }, encodage: { maxBitrate: 2000000, maxFramerate: 15 } },
    fluide:    { budget: 6000000, hint: 'motion', contraintes: { frameRate: { ideal: 30, max: 30 } }, encodage: { maxBitrate: 3000000, maxFramerate: 30 } },
    eco:       { budget: 1000000, hint: 'detail', contraintes: { frameRate: { ideal: 5,  max: 5 } },  encodage: { maxBitrate: 400000,  maxFramerate: 5, scaleResolutionDownBy: 2 } }
};

const DEBIT_MIN = 80000; // en dessous, l'image devient inexploitable

// Les réglages sont appliqués l'un après l'autre : deux setParameters simultanés
// sur le même émetteur échouent (plusieurs participants qui arrivent en même temps).
let fileQualite = Promise.resolve();
function appliquerQualite() {
    fileQualite = fileQualite.then(appliquerQualiteMaintenant, appliquerQualiteMaintenant);
    return fileQualite;
}

let derniereCapture = null;

async function appliquerQualiteMaintenant() {
    if (!localStream) return;
    const ecran = !!screenTrack;
    const choix = ecran ? $('selEcran').value : $('selCam').value;
    const preset = ecran ? QUALITE_ECRAN[choix] : QUALITE_CAM[choix];
    const track = ecran ? screenTrack : cameraTrack();

    // 1. Capture (seulement si la source ou le réglage a changé)
    const cleCapture = track && track.id + '/' + choix;
    if (track && cleCapture !== derniereCapture && !(sansCamera && !ecran)) {
        derniereCapture = cleCapture;
        if (ecran) track.contentHint = preset.hint;
        try { await track.applyConstraints(preset.contraintes); } catch (e) { console.warn('Contraintes refusées', e); }
    }

    // 2. Ce que chaque participant doit recevoir, selon la taille à laquelle il m'affiche
    const hSource = (track && track.getSettings().height) || 720;
    const reduc = preset.encodage.scaleResolutionDownBy || 1;
    const cibles = sendersVideo().map(({ id, sender }) => {
        const v = vues.get(id);                       // inconnue : on suppose « en grand »
        const visible = !v || v.visible;
        const scale = Math.max(reduc, hSource / (v ? v.h : hSource));
        // Le débit nécessaire suit le nombre de pixels (∝ hauteur²)
        const debit = preset.encodage.maxBitrate * Math.min(1, (reduc / scale) ** 2);
        return { sender, visible, scale, debit };
    });

    // 3. Budget d'envoi total : si on le dépasse, tout le monde est réduit proportionnellement
    const total = cibles.filter(c => c.visible).reduce((s, c) => s + c.debit, 0);
    const k = total > preset.budget ? preset.budget / total : 1;

    const preference = ecran && preset.hint === 'detail' ? 'maintain-resolution'
                     : ecran ? 'maintain-framerate' : 'balanced';
    const regler = async (c, avecPreference) => {
        const p = c.sender.getParameters();
        if (!p.encodings || !p.encodings.length) return; // pas encore négocié : réappliqué à la connexion
        const enc = p.encodings[0];
        enc.active = c.visible;                       // personne ne me regarde : je n'envoie rien
        enc.scaleResolutionDownBy = Math.round(c.scale * 100) / 100;
        enc.maxBitrate = Math.round(Math.max(DEBIT_MIN, c.debit * k));
        if (preset.encodage.maxFramerate) enc.maxFramerate = preset.encodage.maxFramerate;
        else delete enc.maxFramerate;
        if (avecPreference) p.degradationPreference = preference;
        await c.sender.setParameters(p);
    };
    await Promise.all(cibles.map(async c => {
        try {
            try {
                await regler(c, true);
            } catch (e) {
                // Certains navigateurs (Firefox) refusent degradationPreference : on réessaie sans
                await regler(c, false);
            }
        } catch (e) {
            console.warn('Réglage encodage impossible', e);
        }
    }));
}

async function partagerEcran() {
    if (screenTrack) return arreterPartage();
    let s;
    try {
        s = await navigator.mediaDevices.getDisplayMedia({ video: true });
    } catch (e) {
        return; // l'utilisateur a annulé
    }
    screenTrack = s.getVideoTracks()[0];
    screenTrack.onended = arreterPartage; // bouton « Arrêter le partage » du navigateur
    await envoyerVideo(screenTrack);
    $('localVideo').srcObject = new MediaStream([screenTrack]);
    $('localVideo').classList.add('ecran');
    majBoutons();
}

function arreterPartage() {
    if (!screenTrack) return;
    screenTrack.onended = null;
    screenTrack.stop();
    screenTrack = null;
    envoyerVideo(cameraTrack());
    $('localVideo').srcObject = localStream;
    $('localVideo').classList.remove('ecran');
    majBoutons();
}

/* =====================================================================
 * Quitter
 * ===================================================================== */

function raccrocher() {
    quitte = true;
    pleinEcran(false);
    epingler(null);
    clearTimeout(timerAnnuaire);
    clearTimeout(timerMoi);
    for (const id of [...appels.keys()]) retirer(id);
    for (const l of liens.values()) l.conn.close();
    liens.clear();
    vues.clear();
    vuesEnvoyees.clear();
    derniereCapture = null;
    if (connAnnuaire) { const c = connAnnuaire; connAnnuaire = null; c.close(); }
    if (annuaire) { const a = annuaire; annuaire = null; a.destroy(); }
    membres = new Map();
    if (moi) { const p = moi; moi = null; p.destroy(); }
    roomId = null;
    cleAuth = null;
    if (screenTrack) { screenTrack.onended = null; screenTrack.stop(); screenTrack = null; }
    $('localVideo').classList.remove('ecran');
    if (localStream) localStream.getTracks().forEach(t => t.stop());
    localStream = null;
    $('localVideo').srcObject = null;
    alerte = '';
    $('call').hidden = true;
    $('setup').hidden = false;
}

/* =====================================================================
 * Boutons
 * ===================================================================== */

function basculer(kind) {
    if (!localStream) return;
    localStream.getTracks().filter(t => t.kind === kind).forEach(t => { t.enabled = !t.enabled; });
    majBoutons();
}

function majBoutons() {
    const actif = kind => localStream && localStream.getTracks().some(t => t.kind === kind && t.enabled);
    $('btnMic').classList.toggle('off', !actif('audio'));
    $('btnCam').classList.toggle('off', sansCamera || !actif('video'));
    $('btnCam').disabled = sansCamera;
    $('btnScreen').textContent = screenTrack ? '⏹️ Arrêter le partage' : "🖥️ Partager l'écran";
    $('btnScreen').classList.toggle('danger', !!screenTrack);
    $('qualiteEcran').hidden = !screenTrack;
    $('selCam').disabled = sansCamera;
}

$('btnJoin').onclick = rejoindre;
$('secretKey').addEventListener('keydown', e => { if (e.key === 'Enter') rejoindre(); });
$('secretKey').addEventListener('input', majForce);
$('pseudo').addEventListener('keydown', e => { if (e.key === 'Enter') $('secretKey').focus(); });
$('btnVoir').onclick = () => {
    const visible = $('secretKey').type === 'text';
    $('secretKey').type = visible ? 'password' : 'text';
    $('btnVoir').textContent = visible ? '👁 Afficher' : '🙈 Masquer';
};
$('btnGenerer').onclick = () => {
    $('secretKey').value = genererCle();
    $('secretKey').type = 'text'; // pour pouvoir la recopier et la transmettre
    $('btnVoir').textContent = '🙈 Masquer';
    majForce();
};
$('btnMic').onclick = () => basculer('audio');
$('btnCam').onclick = () => basculer('video');
$('btnHangup').onclick = raccrocher;
$('btnScreen').onclick = partagerEcran;
$('selCam').onchange = appliquerQualite;
$('selEcran').onchange = appliquerQualite;
// Pas de partage d'écran sur mobile / navigateurs non compatibles
if (!navigator.mediaDevices || !navigator.mediaDevices.getDisplayMedia) $('btnScreen').hidden = true;

/* =====================================================================
 * Application installable (PWA)
 * ===================================================================== */

if ('serviceWorker' in navigator) {
    navigator.serviceWorker.register('sw.js').catch(e => console.warn('Service worker', e));
}

const dejaInstallee = matchMedia('(display-mode: standalone)').matches || navigator.standalone;
let invitationInstall = null;

// Chrome / Edge / Android : on garde l'invitation et on affiche notre bouton
window.addEventListener('beforeinstallprompt', e => {
    e.preventDefault();
    invitationInstall = e;
    $('btnInstall').hidden = false;
});
$('btnInstall').onclick = async () => {
    if (!invitationInstall) return;
    invitationInstall.prompt();
    await invitationInstall.userChoice;
    invitationInstall = null;
    $('btnInstall').hidden = true;
};
window.addEventListener('appinstalled', () => { $('btnInstall').hidden = true; });

// iPhone / iPad : pas d'invitation automatique, on explique la marche à suivre
if (!dejaInstallee && /iphone|ipad|ipod/i.test(navigator.userAgent)) $('iosHint').hidden = false;

/* =====================================================================
 * Plein écran
 * La classe .focus fait la mise en page (participants en grand, ma vignette
 * dans un coin). On demande en plus le vrai plein écran au navigateur quand
 * c'est possible (pas sur iPhone, où la classe seule fait office de plein écran).
 * ===================================================================== */

let reposTimer = null;

function pleinEcran(actif) {
    $('call').classList.toggle('focus', actif);
    $('btnFull').textContent = actif ? '✕ Quitter le plein écran' : '⛶ Plein écran';
    if (actif) {
        if (!document.fullscreenElement && $('call').requestFullscreen) $('call').requestFullscreen().catch(() => {});
        reveiller();
    } else {
        epingler(null);
        clearTimeout(reposTimer);
        $('call').classList.remove('repos');
        if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
    }
}

// Masque les contrôles après 3 s sans bouger la souris
function reveiller() {
    $('call').classList.remove('repos');
    clearTimeout(reposTimer);
    if ($('call').classList.contains('focus')) {
        reposTimer = setTimeout(() => $('call').classList.add('repos'), 3000);
    }
}

$('btnFull').onclick = () => pleinEcran(!$('call').classList.contains('focus'));
['mousemove', 'touchstart', 'keydown'].forEach(ev => $('call').addEventListener(ev, reveiller));
// Sortie via Échap / geste du navigateur : on remet la mise en page normale
document.addEventListener('fullscreenchange', () => {
    if (!document.fullscreenElement && $('call').classList.contains('focus')) pleinEcran(false);
});
document.addEventListener('keydown', e => {
    if (e.key === 'Escape' && $('call').classList.contains('focus')) pleinEcran(false);
});

// Fermeture de l'onglet : on prévient les autres le plus vite possible
window.addEventListener('beforeunload', () => {
    if (annuaire) annuaire.destroy();
    if (moi) moi.destroy();
});
