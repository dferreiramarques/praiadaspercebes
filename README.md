# 🏖 Na Praia das Percebes — Versão Online

Jogo de tile-placement multijogador para 2–4 jogadores.

## Deploy no Render.com

1. Faz push deste repositório para o GitHub
2. No Render, cria um novo **Web Service**
3. Liga ao teu repositório
4. Configurações:
   - **Build Command:** `npm install`
   - **Start Command:** `node server.js`
   - **Environment:** Node
5. Deploy! O jogo fica disponível no URL gerado pelo Render.

## Correr localmente

```bash
npm install
node server.js
```

Abre `http://localhost:3000` no browser.

## Estrutura

```
├── server.js       ← jogo completo (servidor + cliente)
├── package.json
└── public/         ← (opcional) assets estáticos
```

## Funcionalidades

- ✅ 2–4 jogadores em tempo real via WebSocket
- ✅ 5 mesas permanentes
- ✅ Reconexão automática (45s de graça)
- ✅ Todos os tiles: Normal, Prancha de Surf (×2), Rocha (bloqueio)
- ✅ Sistema de salva-vidas (horizontal/vertical)
- ✅ Pontuação final com multiplicadores de prancha e bloqueios de rocha
- ✅ 8 objetivos com revelação progressiva
- ✅ Bónus de fichas restantes
- ✅ Fim de jogo por deck esgotado ou fichas esgotadas
- ✅ PWA (instalável no telemóvel)
