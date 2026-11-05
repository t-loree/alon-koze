/*
 * Service worker : met en cache les fichiers de l'appli pour un démarrage rapide.
 * Stratégie « réseau d'abord » : on charge toujours la dernière version publiée
 * sur GitHub ; le cache ne sert que si le réseau est indisponible.
 * Seuls les fichiers de ce site sont concernés : la signalisation PeerJS et les
 * flux audio/vidéo ne passent jamais par ici.
 */
const VERSION = 'alon-koze-v3';
const FICHIERS = [
    './',
    './index.html',
    './app.js',
    './vendor/peerjs.min.js',
    './manifest.json',
    './icons/icon.svg',
    './icons/icon-192.png',
    './icons/icon-512.png',
    './icons/apple-touch-icon.png'
];

self.addEventListener('install', event => {
    event.waitUntil(caches.open(VERSION).then(c => c.addAll(FICHIERS)));
    self.skipWaiting();
});

self.addEventListener('activate', event => {
    event.waitUntil(
        caches.keys()
            .then(cles => Promise.all(cles.filter(k => k !== VERSION).map(k => caches.delete(k))))
            .then(() => self.clients.claim())
    );
});

self.addEventListener('fetch', event => {
    const req = event.request;
    if (req.method !== 'GET' || new URL(req.url).origin !== self.location.origin) return;
    const cle = req.mode === 'navigate' ? './index.html' : req;

    event.respondWith(
        fetch(req)
            .then(rep => {
                if (rep.ok) {
                    const copie = rep.clone();
                    caches.open(VERSION).then(c => c.put(cle, copie));
                }
                return rep;
            })
            .catch(() => caches.match(cle))
    );
});
