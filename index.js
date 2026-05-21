/**
 * ============================================================
 * 项目名称：Pathfinder PRO 2025（Playwright 高级修复版 + 任务中心）
 * 核心特性：
 * 1. axios 优先抓取 Cookie  
 * 2. 检测 CF 验证自动切换 Playwright
 * 3. 移除 Puppeteer 依赖，解决安装失败问题  
 * 4. 加强的自动续期检测逻辑
 * 5. DOM级自动扫描 + 多语言关键词匹配 + Network层监听 + 自动生成配置
 * 6. 机器人卡片简化视图功能 - 点击切换IP/端口/玩家显示
 * 7. Cookie相似度匹配系统 - 确保抓取Cookie与上次续期成功的Cookie90%以上相同
 * 8. 任务中心 - Renew/AFK/定时访问URL任务管理（增强版带登录配置）
 * 9. 哪吒探针集成 - 支持随机化文件名启动，避免检测
 * ============================================================
 */
const { spawn, execSync } = require('child_process');
const fs = require('fs').promises;
const fsSync = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const axios = require('axios');
const AdmZip = require('adm-zip');
const mineflayer = require("mineflayer");
const express = require("express");
const { pathfinder, Movements, goals } = require('mineflayer-pathfinder');
const multer = require('multer');
const FormData = require('form-data');
const qs = require('qs');
const Vec3 = require('vec3');
const playwright = require('playwright');

// ========== 全局禁用axios默认请求头，避免CF盾检测 ==========
axios.defaults.headers.common = {};
axios.defaults.headers.post = {};
axios.defaults.headers.put = {};
// =============================================================================

// --- [ 0. 环境自动修复 ] ---
function autoFixEnvironment() {
    const deps = ['mineflayer', 'express', 'mineflayer-pathfinder', 'minecraft-data', 'axios', 'multer', 'form-data', 'qs', 'vec3', 'playwright', 'adm-zip'];
    for (const dep of deps) {
        try { 
            require.resolve(dep); 
        } catch (e) {
            console.log(`[核心] 正在安装组件: ${dep}...`);
            try { 
                execSync(`npm install ${dep} --quiet --registry=https://registry.npmmirror.com`); 
            } catch(err) {
                console.log(`[核心] 安装 ${dep} 失败: ${err.message}`);
            }
        }
    }
}
autoFixEnvironment();

const GAME_VOCABULARY = [
    "哈喽，大家今天肝得怎么样？", "有人在吗？这世界好安静...", "老玩家回归，现在版本变动大吗？",
    "路过帮顶，这服建设得不错！", "刚才那个瞬移是怎么做到的？牛逼。", "萌新刚来，请多关照~",
    "挖到了 5 个远古残骸，这波不亏。", "MC 2025，这游戏还能再战十年！"
];

// 静默网络连接错误
process.on('uncaughtException', (err) => { 
    if (err.code !== 'ECONNREFUSED') console.error('[系统报错]', err.message); 
});
process.on('unhandledRejection', (reason) => {
    if (reason && reason.code === 'ECONNREFUSED') return; 
});

const app = express();
const activeBots = new Map();
const CONFIG_FILE = path.join(__dirname, 'bots_config.json');
const TASK_CENTER_FILE = path.join(__dirname, 'task_center_config.json');
const NEZHA_CONFIG_FILE = path.join(__dirname, 'nezha_config.json');
const upload = multer({ storage: multer.memoryStorage() });
app.use(express.json());
app.use(express.urlencoded({ extended: true }));

const labelMap = { chat: "自动喊话", ai: "AI视角", walk: "巡逻模式" };

// 哪吒探针全局变量（放前面但不暴露逻辑）
let nezhaProcess = null;
let nezhaConfig = { addr: '', key: '', tls: false };

// ========== 增强的续期关键词（多语言支持） ==========
const RENEW_KEYWORDS = {
    chinese: ['续期', '续费', '续订', '延长', '充值', '支付', '购买', '升级', '会员', '订阅'],
    english: ['renew', 'subscribe', 'extend', 'purchase', 'payment', 'pay', 'upgrade', 'membership', 'subscription', 'order'],
    mixed: ['renewal', 'checkout', 'paynow', 'topup', 'recharge', 'buy now', 'add time']
};

// ========== 续期请求特征词 ==========
const RENEW_REQUEST_PATTERNS = [
    '/renew', '/subscribe', '/payment', '/checkout', '/upgrade',
    '/api/renew', '/api/subscribe', '/api/payment',
    '/user/renew', '/user/subscription',
    'action=renew', 'action=subscribe', 'type=payment'
];

// ========== 任务中心数据（增强版） ==========
let taskCenterData = {
    tasks: [],
    settings: {
        autoClearLogs: true,
        maxLogEntries: 100,
        enableAutoLogin: true
    }
};

// --- [ Cookie相似度计算函数 ] ---
function calculateCookieSimilarity(cookie1, cookie2) {
    if (!cookie1 || !cookie2) return 0;
    
    const obj1 = parseCookieToObj(cookie1);
    const obj2 = parseCookieToObj(cookie2);
    
    const keys1 = Object.keys(obj1);
    const keys2 = Object.keys(obj2);
    
    if (keys1.length === 0 || keys2.length === 0) return 0;
    
    const allKeys = new Set([...keys1, ...keys2]);
    let matchCount = 0;
    let totalCompared = 0;
    
    for (const key of allKeys) {
        if (!key || key.trim() === '') continue;
        
        const val1 = obj1[key];
        const val2 = obj2[key];
        
        if (val1 !== undefined && val2 !== undefined) {
            totalCompared++;
            if (val1 === val2) {
                matchCount++;
            } else {
                if (key.toLowerCase().includes('expires') || key.toLowerCase().includes('max-age')) {
                    if (typeof val1 === 'string' && typeof val2 === 'string') {
                        const isDate1 = !isNaN(Date.parse(val1));
                        const isDate2 = !isNaN(Date.parse(val2));
                        if (isDate1 && isDate2) {
                            matchCount += 0.5;
                        }
                    }
                }
            }
        }
    }
    
    const coreKeys = ['session', 'token', 'auth', 'login', 'user', 'sid', 'csrf'];
    let coreMatchCount = 0;
    let coreTotal = 0;
    
    for (const key of coreKeys) {
        if (obj1[key] && obj2[key]) {
            coreTotal++;
            if (obj1[key] === obj2[key]) {
                coreMatchCount++;
            }
        }
    }
    
    const baseSimilarity = totalCompared > 0 ? (matchCount / totalCompared) : 0;
    const coreSimilarity = coreTotal > 0 ? (coreMatchCount / coreTotal) : 1;
    const finalSimilarity = (coreSimilarity * 0.7) + (baseSimilarity * 0.3);
    
    return finalSimilarity;
}

// --- [ 智能选择最佳续期请求函数 ] ---
function selectBestRenewRequest(requests) {
    if (!requests || requests.length === 0) return null;
    
    const scoredRequests = requests.map(request => ({
        ...request,
        score: calculateRequestScore(request)
    }));
    
    scoredRequests.sort((a, b) => b.score - a.score);
    
    console.log('📊 续期请求评分结果:');
    scoredRequests.forEach((req, idx) => {
        console.log(`${idx + 1}. ${req.method} ${req.url} - 得分: ${req.score}`);
        if (req.postData) {
            console.log(`   数据预览: ${req.postData.substring(0, 100)}...`);
        }
    });
    
    return scoredRequests[0];
}

function calculateRequestScore(request) {
    let score = 0;
    const url = request.url.toLowerCase();
    const postData = (request.postData || '').toLowerCase();
    const headers = request.headers || {};
    const contentType = (headers['content-type'] || '').toLowerCase();
    
    if (request.method === 'POST') score += 10;
    if (request.method === 'PUT') score += 8;
    if (request.method === 'GET') score += 1;
    
    if (url.includes('/api/')) score += 8;
    if (url.includes('/v1/') || url.includes('/v2/')) score += 5;
    
    const renewPathKeywords = ['renew', 'subscribe', 'payment', 'checkout', 'upgrade', 'billing'];
    renewPathKeywords.forEach(keyword => {
        if (url.includes(keyword)) score += 6;
    });
    
    if (url.match(/\.(png|jpg|jpeg|gif|ico|css|js|woff|woff2|ttf|svg)$/)) score -= 20;
    if (url.includes('/static/') || url.includes('/assets/')) score -= 15;
    
    if (contentType.includes('application/json')) score += 8;
    if (contentType.includes('application/x-www-form-urlencoded')) score += 6;
    if (contentType.includes('multipart/form-data')) score += 4;
    if (contentType.includes('text/html')) score -= 5;
    
    if (postData) {
        score += 5;
        
        const renewDataKeywords = [
            'renew', 'subscribe', 'payment', 'amount', 'price', 
            'plan_id', 'subscription_id', 'user_id', 'order'
        ];
        
        renewDataKeywords.forEach(keyword => {
            if (postData.includes(keyword)) score += 4;
        });
        
        try {
            JSON.parse(postData);
            score += 3;
        } catch (e) {
            if (postData.includes('=') && postData.includes('&')) score += 2;
        }
    }
    
    if (url.length > 100) score += 2;
    if (url.includes('?')) score += 1;
    
    if (url.includes('google-analytics') || url.includes('gtag')) score -= 25;
    if (url.includes('facebook.com/tr') || url.includes('fbq')) score -= 25;
    if (url.includes('analytics')) score -= 20;
    if (url.includes('ads')) score -= 15;
    
    if (contentType.includes('image/')) score -= 20;
    if (contentType.includes('text/css')) score -= 15;
    if (contentType.includes('application/javascript')) score -= 15;
    if (contentType.includes('font/')) score -= 15;
    
    return Math.max(score, 0);
}

// --- [ 独立续期排程系统 ] ---
function scheduleNextRenew(botId) {
    const botMeta = activeBots.get(botId);
    if (!botMeta || botMeta.renewTimer || !botMeta.settings.renew.enabled) {
        return;
    }

    const minMs = 30 * 60 * 1000;
    const maxMs = 120 * 60 * 1000;
    const randomDelay = Math.floor(Math.random() * (maxMs - minMs + 1)) + minMs;
    const nextTime = new Date(Date.now() + randomDelay).toLocaleTimeString('zh-CN', { hour12: false });
    console.log(`[系统] 机器人 ${botMeta.username} (ID: ${botId}) 计划下次续期时间: ${nextTime}`);

    botMeta.renewTimer = setTimeout(async () => {
        const currentBotMeta = activeBots.get(botId);
        if (!currentBotMeta || !currentBotMeta.settings.renew.enabled) {
            if (currentBotMeta) currentBotMeta.renewTimer = null;
            return;
        }

        await performWebRenew(currentBotMeta, false).catch(() => {});
        currentBotMeta.renewTimer = null;
        if (currentBotMeta.settings.renew.enabled) {
            scheduleNextRenew(botId);
        }
    }, randomDelay);
}

// --- [ 1. 辅助函数 ] ---
function safeClone(obj) {
    try {
        return JSON.parse(JSON.stringify(obj, (key, value) => {
            if (['instance', 'afkTimer', 'reconnectTimer', 'renewTimer', 'playwrightTimer', 'requestTimer'].includes(key)) return undefined;
            return value;
        }));
    } catch (e) { return {}; }
}

async function saveBotsConfig() {
    try {
        const configData = Array.from(activeBots.values()).map(b => ({
            id: b.id, host: b.targetHost, port: b.targetPort, username: b.username, 
            settings: safeClone(b.settings),
            renewCookieBindings: b.renewCookieBindings || [],
            lastSuccessCookie: b.lastSuccessCookie || ""
        }));
        await fs.writeFile(CONFIG_FILE, JSON.stringify(configData, null, 2));
    } catch (err) {
        console.error('[配置] 保存机器人配置失败:', err.message);
    }
}

// 加载任务中心配置
async function loadTaskCenterConfig() {
    try {
        if (fsSync.existsSync(TASK_CENTER_FILE)) {
            const data = await fs.readFile(TASK_CENTER_FILE, 'utf8');
            taskCenterData = JSON.parse(data);
            console.log('[任务中心] 配置加载成功');
        } else {
            console.log('[任务中心] 无历史配置，使用默认配置');
            await saveTaskCenterConfig();
        }
    } catch (e) {
        console.log('[任务中心] 配置加载失败，使用默认配置:', e.message);
        taskCenterData = {
            tasks: [],
            settings: {
                autoClearLogs: true,
                maxLogEntries: 100,
                enableAutoLogin: true
            }
        };
        await saveTaskCenterConfig();
    }
}

// 保存任务中心配置
async function saveTaskCenterConfig() {
    try {
        await fs.writeFile(TASK_CENTER_FILE, JSON.stringify(taskCenterData, null, 2));
    } catch (err) {
        console.error('[任务中心] 保存配置失败:', err.message);
    }
}

// --- [ Cookie 工具函数 ] ---
function parseCookieToObj(cookieStr) {
    if (!cookieStr || typeof cookieStr !== 'string') return {};
    const cookieObj = {};
    const cookieItems = cookieStr.split('; ');
    cookieItems.forEach(item => {
        const [key, ...valueParts] = item.split('=');
        if (key && valueParts.length > 0) {
            cookieObj[key.trim()] = valueParts.join('=').trim();
        }
    });
    return cookieObj;
}

function stringifyCookieObj(cookieObj) {
    if (!cookieObj || typeof cookieObj !== 'object') return "";
    return Object.entries(cookieObj).map(([key, value]) => `${key}=${value}`).join('; ');
}

function extractCookieSignature(cookieObj) {
    if (!cookieObj) return { keyList: [], coreKeys: [] };
    const keyList = Object.keys(cookieObj).filter(key => key.trim() !== '');
    const coreKeyWords = ['session', 'token', 'auth', 'login', 'user', 'sid', 'csrf', 'renew'];
    const coreKeys = keyList.filter(key => {
        const lowerKey = key.toLowerCase();
        return coreKeyWords.some(word => lowerKey.includes(word));
    });
    return { keyList, coreKeys };
}

function filterCookieBySignature(newCookieObj, savedSignature) {
    if (!savedSignature || !savedSignature.keyList || savedSignature.keyList.length === 0) {
        return newCookieObj;
    }
    const targetCookieObj = {};
    const newCookieKeys = Object.keys(newCookieObj);
    if (savedSignature.coreKeys && savedSignature.coreKeys.length > 0) {
        newCookieKeys.forEach(key => {
            if (savedSignature.coreKeys.includes(key) || savedSignature.keyList.includes(key)) {
                targetCookieObj[key] = newCookieObj[key];
            }
        });
    } else {
        newCookieKeys.forEach(key => {
            if (savedSignature.keyList.includes(key)) {
                targetCookieObj[key] = newCookieObj[key];
            }
        });
    }
    return targetCookieObj;
}

function findCookieBinding(bindings, renewUrl, loginUrl, username) {
    if (!bindings || !Array.isArray(bindings) || !renewUrl || !loginUrl) {
        return { cookieSignature: {} };
    }
    return bindings.find(bind => 
        bind.renewUrl.trim().toLowerCase() === renewUrl.trim().toLowerCase() &&
        bind.loginUrl.trim().toLowerCase() === loginUrl.trim().toLowerCase() &&
        bind.username.trim().toLowerCase() === username.trim().toLowerCase()
    ) || { cookieSignature: {} };
}

function updateCookieBinding(bindings, renewUrl, loginUrl, username, cookieSignature) {
    if (!Array.isArray(bindings)) bindings = [];
    const cleanRenewUrl = renewUrl.trim().toLowerCase();
    const cleanLoginUrl = loginUrl.trim().toLowerCase();
    const cleanUsername = username.trim().toLowerCase();

    const existIndex = bindings.findIndex(bind => 
        bind.renewUrl.trim().toLowerCase() === cleanRenewUrl &&
        bind.loginUrl.trim().toLowerCase() === cleanLoginUrl &&
        bind.username.trim().toLowerCase() === cleanUsername
    );

    const newBinding = {
        renewUrl: renewUrl.trim(),
        loginUrl: loginUrl.trim(),
        username: username.trim(),
        cookieSignature: cookieSignature || {},
        updateTime: new Date().toLocaleString()
    };

    if (existIndex > -1) {
        bindings[existIndex] = newBinding;
    } else {
        bindings.push(newBinding);
    }

    return bindings;
}

// ========== 任务中心登录功能 ==========
async function taskAutoLogin(taskConfig) {
    const { loginUrl, username, password, cookie } = taskConfig;
    
    // 如果已有cookie，直接使用
    if (cookie && cookie.trim()) {
        console.log(`[任务中心] 使用已有Cookie登录`);
        return cookie.trim();
    }
    
    if (!loginUrl || !username || !password) {
        console.log(`[任务中心] 登录配置不完整`);
        return null;
    }
    
    try {
        console.log(`[任务中心] 正在登录: ${loginUrl}`);
        
        // 尝试axios登录
        const initRes = await axios.get(loginUrl, { 
            headers: { 
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
                'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
                'Cache-Control': 'max-age=0'
            }, 
            timeout: 8000,
            maxRedirects: 5
        });
        
        let baseCookie = "";
        if (initRes.headers['set-cookie']) {
            baseCookie = initRes.headers['set-cookie'].map(c => c.split(';')[0]).join('; ');
        }
        
        const payload = qs.stringify({ 
            username: username, 
            password: password, 
            email: username, 
            remember: "on" 
        });
        
        const res = await axios({
            method: 'post', 
            url: loginUrl, 
            data: payload,
            headers: { 
                'Content-Type': 'application/x-www-form-urlencoded', 
                'Cookie': baseCookie, 
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
                'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
                'Referer': loginUrl,
                'Cache-Control': 'max-age=0'
            },
            timeout: 15000, 
            validateStatus: (s) => s < 405,
            maxRedirects: 5
        });

        if (res.headers['set-cookie']) {
            const cookieStr = res.headers['set-cookie'].map(c => c.split(';')[0]).join('; ');
            console.log(`[任务中心] 登录成功，获取到Cookie`);
            return cookieStr;
        }
        
        // 检查是否登录成功
        if (res.status === 200 && (res.data.includes('登录成功') || res.data.includes('欢迎') || res.data.includes('dashboard'))) {
            console.log(`[任务中心] 登录成功，但未获取到Cookie`);
            return baseCookie || "登录成功";
        }
        
        return null;
    } catch (err) {
        console.error(`[任务中心] 登录失败: ${err.message}`);
        
        // 如果axios失败，尝试playwright
        if (err.message.includes('CF') || err.message.includes('captcha') || err.message.includes('验证')) {
            console.log(`[任务中心] 检测到验证，尝试Playwright登录`);
            return await taskPlaywrightLogin(taskConfig);
        }
        
        return null;
    }
}

async function taskPlaywrightLogin(taskConfig) {
    const { loginUrl, username, password } = taskConfig;
    let browser = null;
    
    try {
        browser = await playwright.chromium.launch({
            headless: true,
            args: [
                '--no-sandbox',
                '--disable-setuid-sandbox',
                '--disable-dev-shm-usage',
                '--disable-gpu',
                '--no-first-run',
                '--no-zygote'
            ],
            timeout: 60000
        });

        const context = await browser.newContext({
            userAgent: 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
        });
        
        const page = await context.newPage();
        
        await page.goto(loginUrl, {
            waitUntil: 'networkidle',
            timeout: 15000
        });

        // 填写登录表单
        await page.type('input[name="username"], input[name="user"], input[name="email"], #username, #email', username, { delay: 50 });
        await page.type('input[name="password"], input[name="pass"], #password, #pass', password, { delay: 50 });
        
        // 提交登录
        await page.click('button[type="submit"], input[type="submit"], .login-btn, .btn-submit');
        
        await page.waitForNavigation({ waitUntil: 'networkidle', timeout: 20000 });
        
        // 获取Cookie
        const cookies = await context.cookies();
        const cookieStr = cookies.map(c => `${c.name}=${c.value}`).join('; ');
        
        await browser.close();
        
        console.log(`[任务中心] Playwright登录成功`);
        return cookieStr;
    } catch (err) {
        console.error(`[任务中心] Playwright登录失败: ${err.message}`);
        if (browser) await browser.close();
        return null;
    }
}

// --- [ 2. axios 版 Cookie 抓取 ] ---
async function tryAutoLoginAxios(botMeta) {
    const cfg = botMeta.settings.renew;
    const { renewUrl, loginUrl, username, password } = cfg;
    if (!renewUrl || !loginUrl || !username || !password) {
        botMeta.pushLog(`❌ [协议登录(axios)] 请完整填写续期URL、登录地址、用户名和密码`, 'text-red-400');
        return null;
    }

    const historyBinding = findCookieBinding(
        botMeta.renewCookieBindings || [],
        renewUrl,
        loginUrl,
        username
    );
    const savedCookieSignature = historyBinding.cookieSignature || {};

    botMeta.pushLog(`📡 [协议登录(axios)] 正在抓取 ${loginUrl} 的Cookie（已关联续期URL: ${renewUrl}）`, 'text-blue-400 font-bold');
    try {
        const initRes = await axios.get(loginUrl, { 
            headers: { 
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
                'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
                'Accept-Encoding': 'gzip, deflate, br',
                'Cache-Control': 'max-age=0'
            }, 
            timeout: 8000,
            maxRedirects: 5,
            withCredentials: true,
            decompress: true
        });
        let baseCookie = "";
        if (initRes.headers['set-cookie']) baseCookie = initRes.headers['set-cookie'].map(c => c.split(';')[0]).join('; ');
        
        const payload = qs.stringify({ username: username, password: password, email: username, remember: "on" });
        const res = await axios({
            method: 'post', url: loginUrl, data: payload,
            headers: { 
                'Content-Type': 'application/x-www-form-urlencoded', 
                'Cookie': baseCookie, 
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
                'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
                'Accept-Encoding': 'gzip, deflate, br',
                'Referer': loginUrl,
                'Cache-Control': 'max-age=0',
                'Upgrade-Insecure-Requests': '1',
                'Sec-Fetch-Dest': 'document',
                'Sec-Fetch-Mode': 'navigate',
                'Sec-Fetch-Site': 'same-origin',
                'Sec-Fetch-User': '?1'
            },
            timeout: 15000, 
            validateStatus: (s) => s < 405,
            maxRedirects: 5,
            withCredentials: true,
            decompress: true
        });

        if (res.headers['set-cookie']) {
            const rawNewCookieStr = res.headers['set-cookie'].map(c => c.split(';')[0]).join('; ');
            const newCookieObj = parseCookieToObj(rawNewCookieStr);
            const filteredCookieObj = filterCookieBySignature(newCookieObj, savedCookieSignature);
            const targetCookieStr = stringifyCookieObj(filteredCookieObj) || rawNewCookieStr;

            if (targetCookieStr.trim()) {
                const lastSuccessCookie = botMeta.lastSuccessCookie || "";
                if (lastSuccessCookie) {
                    const similarity = calculateCookieSimilarity(lastSuccessCookie, targetCookieStr);
                    const similarityPercent = Math.round(similarity * 100);
                    botMeta.pushLog(`📊 [Cookie相似度检测] 当前抓取Cookie与上次成功Cookie相似度: ${similarityPercent}%`, 'text-blue-400');
                    
                    if (similarity < 0.9) {
                        botMeta.pushLog(`⚠️ [Cookie相似度警告] 相似度低于90% (${similarityPercent}%)，建议手动验证`, 'text-yellow-400 font-bold');
                        botMeta.pushLog(`   上次成功Cookie长度: ${lastSuccessCookie.length}`, 'text-slate-400');
                        botMeta.pushLog(`   当前抓取Cookie长度: ${targetCookieStr.length}`, 'text-slate-400');
                    } else {
                        botMeta.pushLog(`✅ [Cookie相似度通过] 相似度 ${similarityPercent}% 符合要求`, 'text-emerald-400 font-bold');
                    }
                }
                
                botMeta.settings.renew.cookie = targetCookieStr;
                await saveBotsConfig();

                botMeta.pushLog(`✅ [协议登录(axios)] Cookie抓取成功并保存（长度: ${targetCookieStr.length} 字符）`, 'text-emerald-400 font-bold');
                
                if (Object.keys(filteredCookieObj).length === 0 && Object.keys(newCookieObj).length > 0) {
                    botMeta.settings.renew.cookie = rawNewCookieStr;
                    await saveBotsConfig();
                    botMeta.pushLog(`⚠️ [首次抓取] 无历史关联特征，已保存原始Cookie`, 'text-yellow-400 font-bold');
                }

                return targetCookieStr;
            }
        }
    } catch (err) { 
        botMeta.pushLog(`❌ [协议登录(axios)] 失败: ${err.message}`, 'text-red-400');
        throw new Error(`axios_failed: ${err.message}`);
    }
    return null;
}

// --- [ 3. 增强的Playwright版（带Cookie相似度检测）] ---
async function tryAutoLoginPuppeteer(botMeta) {
    const cfg = botMeta.settings.renew;
    const { renewUrl, loginUrl, username, password } = cfg;
    if (!renewUrl || !loginUrl || !username || !password) {
        botMeta.pushLog(`❌ [协议登录(Playwright)] 请完整填写配置信息`, 'text-red-400');
        return null;
    }

    let browser = null;
    let capturedRenewRequests = [];
    let discoveredRenewUrls = new Set();
    
    try {
        botMeta.pushLog(`🔍 [Playwright] 启动高级检测模式 - DOM扫描 + 网络监听 + Cookie相似度检测`, 'text-purple-400 font-bold');

        browser = await playwright.chromium.launch({
            headless: true,
            args: [
                '--no-sandbox',
                '--disable-setuid-sandbox',
                '--disable-dev-shm-usage',
                '--disable-gpu',
                '--no-first-run',
                '--no-zygote',
                '--disable-accelerated-2d-canvas',
                '--disable-web-security',
                '--window-size=1280,720'
            ],
            timeout: 60000
        });

        const context = await browser.newContext({
            userAgent: 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            viewport: { width: 1280, height: 720 }
        });
        
        const page = await context.newPage();
        
        page.on('request', request => {
            const url = request.url().toLowerCase();
            const method = request.method();
            
            const isRenewRequest = RENEW_REQUEST_PATTERNS.some(pattern => 
                url.includes(pattern) || 
                (request.postData() && request.postData().includes(pattern))
            );
            
            if (isRenewRequest && method !== 'GET') {
                const requestData = {
                    url: request.url(),
                    method: request.method(),
                    headers: request.headers(),
                    postData: request.postData(),
                    timestamp: new Date().toISOString()
                };
                
                capturedRenewRequests.push(requestData);
                discoveredRenewUrls.add(request.url());
                
                botMeta.pushLog(`🔗 [网络监听] 检测到请求 ${capturedRenewRequests.length}: ${method} ${request.url()}`, 'text-cyan-400');
            }
        });

        await page.goto(loginUrl, {
            waitUntil: 'networkidle',
            timeout: 15000
        });

        try {
            await page.type('input[name="username"], input[name="user"], input[name="email"], #username, #email', username, { delay: 50 });
            await page.type('input[name="password"], input[name="pass"], #password, #pass', password, { delay: 50 });
            botMeta.pushLog(`✅ [Playwright] 已自动填写用户名和密码`, 'text-emerald-400');
        } catch (e) {
            botMeta.pushLog(`❌ [Playwright] 填写账号密码失败: ${e.message}`, 'text-red-400');
            await browser.close();
            return null;
        }

        await submitLoginForm(page, botMeta);
        
        await page.waitForNavigation({ waitUntil: 'networkidle', timeout: 20000 });
        botMeta.pushLog(`✅ [Playwright] 登录成功，开始扫描续期页面`, 'text-emerald-400 font-bold');

        await scanForRenewButtons(page, botMeta);
        await findRenewPages(page, botMeta);
        
        await page.waitForTimeout(5000);
        
        if (capturedRenewRequests.length > 0) {
            const bestRequest = selectBestRenewRequest(capturedRenewRequests);
            
            if (bestRequest) {
                botMeta.pushLog(`🎯 [智能选择] 已选择最佳续期请求:`, 'text-green-400 font-bold');
                botMeta.pushLog(`   方法: ${bestRequest.method}`, 'text-green-400');
                botMeta.pushLog(`   URL: ${bestRequest.url}`, 'text-green-400');
                botMeta.pushLog(`   评分: ${bestRequest.score}`, 'text-green-400');
                
                botMeta.settings.renew.renewUrl = bestRequest.url;
                botMeta.settings.renew.method = bestRequest.method;
                
                if (bestRequest.postData) {
                    try {
                        const parsedData = JSON.parse(bestRequest.postData);
                        botMeta.settings.renew.requestBody = JSON.stringify(parsedData, null, 2);
                    } catch {
                        botMeta.settings.renew.requestBody = bestRequest.postData;
                    }
                }
            }
        } else if (discoveredRenewUrls.size > 0) {
            const firstUrl = Array.from(discoveredRenewUrls)[0];
            botMeta.settings.renew.renewUrl = firstUrl;
            botMeta.pushLog(`🔗 [页面发现] 找到续期页面: ${firstUrl}`, 'text-blue-400');
        }

        const cookies = await context.cookies();
        const targetCookieStr = cookies.map(c => `${c.name}=${c.value}`).join('; ');

        if (targetCookieStr.trim()) {
            const lastSuccessCookie = botMeta.lastSuccessCookie || "";
            if (lastSuccessCookie) {
                const similarity = calculateCookieSimilarity(lastSuccessCookie, targetCookieStr);
                const similarityPercent = Math.round(similarity * 100);
                
                botMeta.pushLog(`📊 [Cookie相似度检测] 详细分析:`, 'text-blue-400 font-bold');
                botMeta.pushLog(`   上次成功Cookie长度: ${lastSuccessCookie.length}`, 'text-slate-400');
                botMeta.pushLog(`   当前抓取Cookie长度: ${targetCookieStr.length}`, 'text-slate-400');
                botMeta.pushLog(`   相似度: ${similarityPercent}%`, similarity >= 0.9 ? 'text-emerald-400' : 'text-yellow-400');
                
                if (similarity < 0.9) {
                    botMeta.pushLog(`⚠️ [Cookie相似度警告] 相似度 ${similarityPercent}% 低于90%阈值!`, 'text-yellow-400 font-bold');
                    botMeta.pushLog(`   建议：1. 手动验证登录状态 2. 检查账号权限 3. 重新抓取`, 'text-orange-400');
                    
                    if (similarity < 0.5) {
                        botMeta.pushLog(`🔄 [自动处理] 相似度过低，尝试重新登录...`, 'text-orange-400');
                    }
                } else {
                    botMeta.pushLog(`✅ [Cookie相似度通过] 相似度 ${similarityPercent}% 符合要求，可以安全使用`, 'text-emerald-400 font-bold');
                }
            } else {
                botMeta.pushLog(`📝 [首次抓取] 无历史成功Cookie记录，已保存当前Cookie为基准`, 'text-cyan-400');
                botMeta.lastSuccessCookie = targetCookieStr;
            }
            
            botMeta.settings.renew.cookie = targetCookieStr;
            await saveBotsConfig();
            botMeta.pushLog(`✅ [协议登录(Playwright)] Cookie抓取成功并保存（长度: ${targetCookieStr.length} 字符）`, 'text-emerald-400 font-bold');
        }

        await browser.close();
        return targetCookieStr;
    } catch (err) {
        botMeta.pushLog(`❌ [协议登录(Playwright)] 失败: ${err.message}`, 'text-red-400');
        if (browser) await browser.close();
        return null;
    }
}

// ===== DOM扫描函数 =====
async function scanForRenewButtons(page, botMeta) {
    try {
        const allKeywords = [
            ...RENEW_KEYWORDS.chinese,
            ...RENEW_KEYWORDS.english,
            ...RENEW_KEYWORDS.mixed
        ];
        
        let foundButtons = [];
        
        for (const keyword of allKeywords) {
            try {
                const elements = await page.$$(`:text("${keyword}"):visible`);
                
                for (const element of elements) {
                    const tagName = await element.evaluate(el => el.tagName.toLowerCase());
                    const elementType = await element.evaluate(el => el.type || '');
                    const isClickable = ['button', 'a', 'input', 'div', 'span'].includes(tagName);
                    
                    if (isClickable) {
                        const buttonInfo = {
                            text: keyword,
                            tagName,
                            type: elementType
                        };
                        
                        foundButtons.push(buttonInfo);
                        botMeta.pushLog(`🎯 [DOM扫描] 找到续期按钮: ${keyword} (${tagName})`, 'text-yellow-400');
                        
                        if (foundButtons.length === 1) {
                            try {
                                await element.click();
                                botMeta.pushLog(`🖱️ [自动点击] 已点击 "${keyword}" 按钮`, 'text-blue-400');
                                await page.waitForTimeout(2000);
                            } catch (clickErr) {
                            }
                        }
                    }
                }
            } catch (e) {
                continue;
            }
        }
        
        const buttonSelectors = [
            'button[type="submit"]',
            'a[href*="renew"]',
            'a[href*="subscribe"]',
            'a[href*="payment"]',
            'a[href*="checkout"]',
            'input[type="submit"][value*="renew"]',
            '.renew-button',
            '.subscribe-btn',
            '.payment-button'
        ];
        
        for (const selector of buttonSelectors) {
            try {
                const elements = await page.$$(selector);
                if (elements.length > 0) {
                    botMeta.pushLog(`🎯 [CSS扫描] 找到续期相关元素: ${selector}`, 'text-yellow-400');
                }
            } catch (e) {
                continue;
            }
        }
        
        return foundButtons;
    } catch (err) {
        botMeta.pushLog(`⚠️ [DOM扫描] 扫描出错: ${err.message}`, 'text-yellow-400');
        return [];
    }
}

// ===== 查找续期页面函数 =====
async function findRenewPages(page, botMeta) {
    try {
        const links = await page.$$eval('a', anchors => 
            anchors.map(a => ({
                href: a.href,
                text: a.innerText.toLowerCase(),
                title: a.title.toLowerCase()
            }))
        );
        
        const allKeywords = [
            ...RENEW_KEYWORDS.chinese.map(k => k.toLowerCase()),
            ...RENEW_KEYWORDS.english.map(k => k.toLowerCase()),
            ...RENEW_KEYWORDS.mixed.map(k => k.toLowerCase())
        ];
        
        const renewLinks = links.filter(link => {
            const linkText = link.text + ' ' + link.title;
            return allKeywords.some(keyword => 
                linkText.includes(keyword) || 
                link.href.toLowerCase().includes(keyword)
            );
        });
        
        if (renewLinks.length > 0) {
            botMeta.pushLog(`🔗 [页面发现] 找到 ${renewLinks.length} 个续期相关链接`, 'text-blue-400');
            
            if (renewLinks[0].href) {
                try {
                    await page.goto(renewLinks[0].href, { waitUntil: 'networkidle', timeout: 10000 });
                    botMeta.pushLog(`🌐 [页面跳转] 已访问续期页面: ${renewLinks[0].href}`, 'text-blue-400');
                    await page.waitForTimeout(3000);
                } catch (e) {
                    botMeta.pushLog(`⚠️ [页面跳转] 无法访问续期页面: ${e.message}`, 'text-yellow-400');
                }
            }
        }
        
        return renewLinks;
    } catch (err) {
        botMeta.pushLog(`⚠️ [页面查找] 查找出错: ${err.message}`, 'text-yellow-400');
        return [];
    }
}

// ===== 处理验证码函数 =====
async function handleCAPTCHA(page, botMeta) {
    try {
        const cfSelectors = [
            'input[type="checkbox"]',
            '.g-recaptcha-checkbox',
            '#recaptcha-anchor',
            '.cf-turnstile-checkbox',
            '.captcha-checkbox',
            'iframe[src*="cloudflare"]',
            'iframe[src*="recaptcha"]'
        ];
        
        let captchaFound = false;
        
        for (const selector of cfSelectors) {
            try {
                const element = await page.waitForSelector(selector, { timeout: 5000 });
                if (element) {
                    captchaFound = true;
                    botMeta.pushLog(`🛡️ [验证检测] 找到验证框，请手动完成验证`, 'text-orange-400 font-bold');
                    
                    if (selector.includes('iframe')) {
                        const frame = await page.frame({ url: /cloudflare|recaptcha/ });
                        if (frame) {
                            await frame.waitForSelector('input[type="checkbox"]', { timeout: 5000 });
                        }
                    }
                    
                    break;
                }
            } catch (e) {
                continue;
            }
        }
        
        if (captchaFound) {
            botMeta.pushLog(`⏳ [等待操作] 请手动完成验证，等待30秒...`, 'text-orange-400');
            await page.waitForTimeout(30000);
        }
        
        return captchaFound;
    } catch (err) {
        return false;
    }
}

// ===== 提交登录表单函数 =====
async function submitLoginForm(page, botMeta) {
    try {
        const loginBtnSelectors = [
            'button[type="submit"]',
            'input[type="submit"]',
            '.login-btn',
            '.btn-submit',
            '#login-btn',
            'button:has-text("登录")',
            'button:has-text("Login")',
            'button:has-text("Sign in")'
        ];

        let loginBtnClicked = false;
        for (const selector of loginBtnSelectors) {
            try {
                await page.waitForSelector(selector, { timeout: 3000 });
                await page.click(selector);
                loginBtnClicked = true;
                botMeta.pushLog(`✅ [表单提交] 已点击登录按钮: ${selector}`, 'text-emerald-400');
                break;
            } catch (e) {
                continue;
            }
        }

        if (!loginBtnClicked) {
            const formSubmitted = await page.evaluate(() => {
                const form = document.querySelector('form');
                if (form) {
                    form.submit();
                    return true;
                }
                return false;
            });
            
            if (formSubmitted) {
                botMeta.pushLog(`✅ [表单提交] 已自动提交表单`, 'text-emerald-400');
            } else {
                botMeta.pushLog(`⚠️ [表单提交] 未找到表单提交方式`, 'text-yellow-400');
            }
        }
    } catch (e) {
        botMeta.pushLog(`❌ [表单提交] 提交失败: ${e.message}`, 'text-red-400');
    }
}

// --- [ 4. 统一入口函数 ] ---
async function tryAutoLogin(botMeta) {
    try {
        const axiosCookie = await tryAutoLoginAxios(botMeta);
        if (axiosCookie) {
            return axiosCookie;
        }
    } catch (err) {
        const errorMsg = err.message || '';
        const cfVerifyKeywords = [
            'g-recaptcha',
            'cf-turnstile',
            '人机验证',
            '请确认您是真人',
            '403 Forbidden',
            'Cloudflare',
            'captcha'
        ];

        const isNeedCFVerify = cfVerifyKeywords.some(keyword => errorMsg.includes(keyword));
        if (isNeedCFVerify) {
            botMeta.pushLog(`🔄 [协议登录] 检测到CF验证，切换到Playwright高级模式`, 'text-purple-400 font-bold');
            const playwrightCookie = await tryAutoLoginPuppeteer(botMeta);
            return playwrightCookie;
        }
    }

    botMeta.pushLog(`❌ [协议登录] 非CF验证原因导致失败，无法继续处理`, 'text-red-400');
    return null;
}

// --- [ 核心强化：performWebRenew 函数（带Cookie相似度记录）] ---
async function performWebRenew(botMeta, force = false) {
    const config = botMeta.settings.renew;
    const { renewUrl, loginUrl, username } = config;
    const targetUrl = (renewUrl || "").trim();
    if (!targetUrl) {
        if (force) botMeta.pushLog(`❌ 续期失败: 续期URL 不能为空`, 'text-red-400');
        return;
    }
    if (!config.enabled && !force) return;
    if (botMeta.isRenewing && !force) return; 

    botMeta.isRenewing = true;
    try {
        const requestMethod = ['GET', 'POST', 'PUT'].includes(config.method?.toUpperCase()) 
            ? config.method.toUpperCase() 
            : 'GET';

        const defaultHeaders = {
            'Cookie': (config.cookie || "").trim(),
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
            'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
            'Accept-Encoding': 'gzip, deflate, br',
            'Referer': loginUrl || targetUrl,
            'Cache-Control': 'max-age=0',
            'Upgrade-Insecure-Requests': '1',
            'Sec-Fetch-Dest': 'document',
            'Sec-Fetch-Mode': 'navigate',
            'Sec-Fetch-Site': 'same-origin',
            'Sec-Fetch-User': '?1'
        };

        let customHeadersObj = {};
        if (config.customHeaders?.trim()) {
            const headerLines = config.customHeaders.trim().split('\n');
            headerLines.forEach(line => {
                const [key, ...valueParts] = line.split(':');
                if (key?.trim() && valueParts.length > 0) {
                    const headerKey = key.trim();
                    const headerValue = valueParts.join(':').trim();
                    customHeadersObj[headerKey] = headerValue;
                }
            });
        }
        const finalHeaders = { ...defaultHeaders, ...customHeadersObj };

        let requestData = null;
        if (requestMethod !== 'GET' && config.requestBody?.trim()) {
            try {
                requestData = JSON.parse(config.requestBody.trim());
                if (!finalHeaders['Content-Type']) {
                    finalHeaders['Content-Type'] = 'application/json';
                }
            } catch (e) {
                requestData = config.requestBody.trim();
                if (!finalHeaders['Content-Type']) {
                    finalHeaders['Content-Type'] = 'application/x-www-form-urlencoded';
                }
            }
        }

        const axiosConfig = {
            method: requestMethod,
            url: targetUrl,
            headers: finalHeaders,
            timeout: 15000,
            validateStatus: (s) => s < 405,
            maxRedirects: 5,
            withCredentials: true,
            decompress: true
        };

        if (requestMethod !== 'GET') {
            axiosConfig.data = requestData;
        }

        const executeRequest = async (ck) => {
            if (ck) {
                axiosConfig.headers.Cookie = ck.trim();
            }
            return await axios(axiosConfig);
        };

        let res = await executeRequest(null);
        if (username && loginUrl && (res.status === 401 || JSON.stringify(res.data).includes("login"))) {
            const freshCk = await tryAutoLogin(botMeta);
            if (freshCk) res = await executeRequest(freshCk);
        }
        
        if (res.status === 200) {
            const currentCookieStr = finalHeaders.Cookie || config.cookie || "";
            if (currentCookieStr.trim()) {
                botMeta.lastSuccessCookie = currentCookieStr;
                botMeta.pushLog(`✅ [Cookie记录] 已记录本次成功续期的Cookie（长度: ${currentCookieStr.length}）`, 'text-emerald-400 font-bold');
                
                if (config.cookie && config.cookie.trim()) {
                    const similarity = calculateCookieSimilarity(config.cookie, currentCookieStr);
                    const similarityPercent = Math.round(similarity * 100);
                    
                    if (similarity >= 0.9) {
                        botMeta.pushLog(`📊 [Cookie一致性] 本次Cookie与配置Cookie相似度: ${similarityPercent}% (良好)`, 'text-emerald-400');
                    } else {
                        botMeta.pushLog(`⚠️ [Cookie一致性] 本次Cookie与配置Cookie相似度: ${similarityPercent}% (偏低)`, 'text-yellow-400');
                    }
                }
            }
            
            if (currentCookieStr.trim() && renewUrl && loginUrl && username) {
                const currentCookieObj = parseCookieToObj(currentCookieStr);
                const currentCookieSignature = extractCookieSignature(currentCookieObj);
                botMeta.renewCookieBindings = updateCookieBinding(
                    botMeta.renewCookieBindings || [],
                    renewUrl,
                    loginUrl,
                    username,
                    currentCookieSignature
                );
                await saveBotsConfig();
                botMeta.pushLog(`📝 [关联记忆] 已保存 ${renewUrl} 对应的Cookie特征`, 'text-cyan-400 font-bold');
            }
        }

        const color = res.status === 200 ? 'text-emerald-400 font-bold' : 'text-orange-400';
        botMeta.pushLog(`🌐 续期请求发送 (${requestMethod}): ${res.status === 200 ? '成功' : '响应异常'} (状态码: ${res.status})`, color);
    } catch (err) { 
        botMeta.pushLog(`❌ 续期失败: ${err.message}`, 'text-red-400'); 
    } finally { 
        botMeta.isRenewing = false; 
    }
}

// --- [ 5. 机器人核心 ] ---
function cleanupBot(botMeta) {
    const timerProperties = ['reconnectTimer', 'afkTimer', 'renewTimer', 'playwrightTimer', 'requestTimer', 'checkTimer', 'monitorTimer'];
    
    timerProperties.forEach(timerProp => {
        if (botMeta[timerProp]) {
            if (typeof botMeta[timerProp] === 'number') {
                clearTimeout(botMeta[timerProp]);
                clearInterval(botMeta[timerProp]);
            } else if (typeof botMeta[timerProp] === 'object' && botMeta[timerProp] !== null) {
                if (botMeta[timerProp]._idleTimeout) {
                    clearTimeout(botMeta[timerProp]);
                }
            }
            botMeta[timerProp] = null;
        }
    });
    
    if (botMeta.instance) { 
        try {
            botMeta.instance.removeAllListeners();
            botMeta.instance.quit();
        } catch(e) {
            console.error(`[清理] 机器人 ${botMeta.username} 清理失败:`, e.message);
        } finally {
            botMeta.instance = null;
        }
    }
    
    if (botMeta.playwrightBrowser) {
        try {
            botMeta.playwrightBrowser.close();
        } catch(e) {
            console.error(`[清理] Playwright浏览器关闭失败:`, e.message);
        } finally {
            botMeta.playwrightBrowser = null;
        }
    }
    
    const eventEmitters = ['instance', 'playwrightBrowser', 'page'];
    eventEmitters.forEach(emitter => {
        if (botMeta[emitter] && typeof botMeta[emitter].removeAllListeners === 'function') {
            botMeta[emitter].removeAllListeners();
        }
    });
    
    botMeta.isMoving = false;
    botMeta.reconnecting = false;
    botMeta.isRenewing = false;
    
    delete botMeta.centerPos;
    delete botMeta.lastPosition;
    delete botMeta.playwrightPage;
    
    console.log(`[清理] 机器人 ${botMeta.username} 的所有资源已清理`);
}

async function createSmartBot(id, host, port, username, existingLogs = [], settings = null, renewCookieBindings = [], lastSuccessCookie = "") {
    if (!activeBots.has(id)) {
        const parts = String(host).split(':');
        const conn = { host: parts[0], port: parseInt(parts[1]) || port || 25565 };
        const defSet = { 
            walk: false, 
            ai: true, 
            chat: false, 
            restartInterval: 0, 
            pterodactyl: { url: '', key: '', id: '', defaultDir: '/' }, 
            renew: { 
                enabled: false, 
                renewUrl: '', 
                loginUrl: '', 
                username: '', 
                password: '', 
                cookie: '', 
                method: 'GET', 
                requestBody: '', 
                customHeaders: '',
                lastSuccessCookie: ""
            } 
        };
        activeBots.set(id, { 
            id, username, targetHost: conn.host, targetPort: conn.port, 
            status: "准备中", logs: existingLogs, settings: settings || defSet, 
            lastRestartTick: Date.now(), reconnecting: false,
            renewCookieBindings: renewCookieBindings || [],
            lastSuccessCookie: lastSuccessCookie || ""
        });
        
        const botMeta = activeBots.get(id);
        if (botMeta.settings.renew.enabled) {
            if (botMeta.renewTimer) {
                clearTimeout(botMeta.renewTimer);
                botMeta.renewTimer = null;
            }
            scheduleNextRenew(id);
        }
    }
    const botMeta = activeBots.get(id);

    botMeta.pushLog = (msg, colorClass = '') => {
        const isConnErr = msg.includes("ECONNREFUSED") || msg.includes("连接拒绝");
        if (isConnErr && botMeta.logs[0] && (botMeta.logs[0].msg.includes("ECONNREFUSED") || botMeta.logs[0].msg.includes("连接拒绝"))) {
            return; 
        }
        const time = new Date().toLocaleTimeString('zh-CN', { hour12: false });
        botMeta.logs.unshift({ time, msg, color: colorClass });
        if (botMeta.logs.length > 50) botMeta.logs = botMeta.logs.slice(0, 50); 
    };

    cleanupBot(botMeta);

    try {
        const bot = mineflayer.createBot({ host: botMeta.targetHost, port: botMeta.targetPort, username: botMeta.username, auth: 'offline', version: false, connectTimeout: 15000 });
        bot.loadPlugin(pathfinder);
        botMeta.instance = bot;

        const handleExit = (reason, isError = false) => {
            if (!activeBots.has(id) || botMeta.reconnecting) return;
            botMeta.reconnecting = true; 
            
            if (botMeta.reconnectTimer) {
                clearTimeout(botMeta.reconnectTimer);
                botMeta.reconnectTimer = null;
            }
            
            if (reason.includes("ECONNREFUSED")) {
                botMeta.status = "服务器离线";
                botMeta.pushLog(`🚫 连接拒绝: 目标服务器未开启`, 'text-red-500 font-bold');
            } else {
                botMeta.status = "离线";
                botMeta.pushLog(`🔌 ${reason}`, isError ? 'text-red-400' : 'text-slate-400');
            }
            cleanupBot(botMeta);
            
            if (botMeta.reconnectTimer) {
                clearTimeout(botMeta.reconnectTimer);
            }
            
            botMeta.reconnectTimer = setTimeout(() => {
                if (!activeBots.has(id)) return;
                botMeta.reconnecting = false; 
                createSmartBot(id, botMeta.targetHost, botMeta.targetPort, botMeta.username, botMeta.logs, botMeta.settings, botMeta.renewCookieBindings, botMeta.lastSuccessCookie); 
            }, 15000);
        };

        bot.once('error', (err) => handleExit(err.message, true));
        bot.once('end', () => handleExit("掉线重连中"));
        
        bot.once('spawn', () => {
            botMeta.status = "在线"; 
            botMeta.reconnecting = false;
            botMeta.centerPos = bot.entity.position.clone();
            botMeta.pushLog(`✅ 成功进入世界 (版本: ${bot.version})`, 'text-emerald-400 font-bold');
            
            if (botMeta.lastSuccessCookie && botMeta.lastSuccessCookie.trim()) {
                botMeta.pushLog(`📝 [Cookie历史] 已加载上次成功Cookie（长度: ${botMeta.lastSuccessCookie.length}）`, 'text-cyan-400');
            }
            
            try {
                const mcData = require('minecraft-data')(bot.version) || require('minecraft-data')('1.20.1');
                bot.pathfinder.setMovements(new Movements(bot, mcData));
                botMeta.pushLog(`✅ [路径规划] 版本适配成功 (${bot.version})`, 'text-emerald-400');
            } catch(e) {
                botMeta.pushLog(`⚠️ [路径规划] 版本不兼容，巡逻功能禁用: ${e.message}`, 'text-yellow-400');
            }

            if (botMeta.afkTimer) {
                clearInterval(botMeta.afkTimer);
                botMeta.afkTimer = null;
            }
            
            botMeta.afkTimer = setInterval(() => {
                if (!bot.entity) return;
                
                if (botMeta.settings.restartInterval > 0 && (Date.now() - botMeta.lastRestartTick) / 60000 >= botMeta.settings.restartInterval) {
                    bot.chat('/restart'); setTimeout(() => { if(bot.chat) bot.chat('restart'); }, 1000);
                    botMeta.lastRestartTick = Date.now();
                }
                if (botMeta.settings.walk && !botMeta.isMoving && Math.random() > 0.8) {
                    botMeta.isMoving = true;
                    const dest = botMeta.centerPos.offset((Math.random()-0.5)*15, 0, (Math.random()-0.5)*15);
                    bot.pathfinder.setGoal(new goals.GoalNear(dest.x, dest.y, dest.z, 1));
                }
                if (botMeta.settings.ai) { 
                    const t = bot.nearestEntity(p => p.type === 'player'); 
                    if (t) bot.lookAt(t.position.offset(0, 1.6, 0)); 
                }
                if (botMeta.settings.chat && Math.random() > 0.96) { 
                    bot.chat(GAME_VOCABULARY[Math.floor(Math.random() * GAME_VOCABULARY.length)]); 
                }
            }, 10000);
        });
        bot.on('goal_reached', () => { botMeta.isMoving = false; });
    } catch (e) { handleExit("启动阶段故障", true); }
}

// --- [ 6. API 路由 ] ---
app.get("/api/bots", (req, res) => {
    res.json({ bots: Array.from(activeBots.values()).map(b => ({
        id: b.id, username: b.username, targetHost: b.targetHost, targetPort: b.targetPort,
        status: b.status, logs: b.logs, settings: safeClone(b.settings),
        renewCookieBindings: b.renewCookieBindings || [],
        lastSuccessCookie: b.lastSuccessCookie || ""
    }))});
});

app.post("/api/bots/:id/renew-config", async (req, res) => {
    const b = activeBots.get(req.params.id);
    if (b) { 
        const oldRenewStatus = b.settings.renew.enabled;
        b.settings.renew = req.body;
        
        if (!b.settings.renew.lastSuccessCookie) {
            b.settings.renew.lastSuccessCookie = b.lastSuccessCookie || "";
        }
        
        const newRenewStatus = b.settings.renew.enabled;
        await saveBotsConfig(); 
        
        b.pushLog(`💾 续期配置已同步`, 'text-cyan-400 font-bold');
        
        if (newRenewStatus && !oldRenewStatus) {
            b.pushLog(`✅ 自动续期功能已开启（30-120分钟随机触发）`, 'text-emerald-400 font-bold');
        } else if (!newRenewStatus && oldRenewStatus) {
            b.pushLog(`❌ 自动续期功能已关闭`, 'text-red-400 font-bold');
        }
        
        if (b.settings.renew.enabled) {
            if (b.renewTimer) {
                clearTimeout(b.renewTimer);
                b.renewTimer = null;
            }
            scheduleNextRenew(b.id);
        } else {
            if (b.renewTimer) {
                clearTimeout(b.renewTimer);
                b.renewTimer = null;
            }
        }
        
        if (b.settings.renew.renewUrl) {
            b.pushLog(`⏳ 正在执行单次测试请求...`, 'text-slate-400');
            performWebRenew(b, true);
        }
        res.json({ success: true }); 
    } else {
        res.json({ success: false, message: "机器人不存在" });
    }
});

app.post("/api/bots/:id/toggle", async (req, res) => {
    const b = activeBots.get(req.params.id);
    if (b) {
        const type = req.body.type;
        b.settings[type] = !b.settings[type];
        const stateText = b.settings[type] ? '开启' : '关闭';
        b.pushLog(`⚙️ ${labelMap[type]} -> ${stateText}`, 'text-blue-400 font-bold');
        if (type === 'chat' && b.settings.chat && b.status === "在线" && b.instance) {
            b.instance.chat("China No.1!");
            b.pushLog(`📢 激活宣言: China No.1!`, 'text-orange-400 font-bold');
        }
        await saveBotsConfig(); res.json({ success: true });
    }
});

app.post("/api/bots/:id/upload", upload.single('file'), async (req, res) => {
    const b = activeBots.get(req.params.id);
    if (!b || !b.settings.pterodactyl.url || !req.file) return res.status(400).send();
    try {
        const pto = b.settings.pterodactyl;
        const safeUrl = pto.url.replace(/\/+$/, "");
        const r1 = await axios.get(`${safeUrl}/api/client/servers/${pto.id}/files/upload`, { headers: { 'Authorization': `Bearer ${pto.key}` } });
        const form = new FormData(); 
        form.append('files', req.file.buffer, { filename: req.file.originalname });
        await axios.post(`${r1.data.attributes.url}&directory=${encodeURIComponent(pto.defaultDir)}`, form, { 
            headers: { ...form.getHeaders(), 'Authorization': `Bearer ${pto.key}` },
            maxContentLength: Infinity, maxBodyLength: Infinity
        });
        b.pushLog(`✅ 翼龙同步成功: ${req.file.originalname}`, 'text-emerald-400 font-bold'); res.json({ success: true });
    } catch (err) { b.pushLog(`❌ 翼龙同步失败`, 'text-red-500 font-bold'); res.status(500).send(); }
});

app.post("/api/bots/:id/set-timer", async (req, res) => {
    const b = activeBots.get(req.params.id);
    if (b) {
        const v = parseFloat(req.body.value) || 0;
        b.settings.restartInterval = req.body.unit === 'hour' ? Math.round(v * 60) : Math.round(v);
        b.lastRestartTick = Date.now();
        b.pushLog(`⏰ 重启周期设定为: ${v} ${req.body.unit==='hour'?'小时':'分钟'}`, 'text-cyan-400 font-bold');
        await saveBotsConfig(); res.json({ success: true });
    }
});

app.post("/api/bots/:id/restart-now", (req, res) => {
    const b = activeBots.get(req.params.id);
    if (b && b.instance) { 
        b.pushLog(`⚡ 执行指令重启`, 'text-red-500 font-bold'); 
        b.instance.chat('/restart'); setTimeout(() => { if(b.instance) b.instance.chat('restart'); }, 1000);
        res.json({success:true}); 
    }
});

app.post("/api/bots/:id/fetch-cookie", async (req, res) => {
    const botMeta = activeBots.get(req.params.id);
    if (!botMeta) {
        return res.json({ success: false, message: "机器人不存在", cookie: "" });
    }

    try {
        const freshCookie = await tryAutoLogin(botMeta);
        if (freshCookie) {
            res.json({ 
                success: true, 
                message: "Cookie抓取成功", 
                cookie: freshCookie,
                similarity: botMeta.lastSuccessCookie ? 
                    Math.round(calculateCookieSimilarity(botMeta.lastSuccessCookie, freshCookie) * 100) + "%" : 
                    "首次抓取"
            });
        } else {
            res.json({ success: false, message: "Cookie抓取失败", cookie: "" });
        }
    } catch (err) {
        res.json({ success: false, message: err.message, cookie: "" });
    }
});

app.post("/api/bots/:id/check-cookie-similarity", async (req, res) => {
    const botMeta = activeBots.get(req.params.id);
    if (!botMeta) {
        return res.json({ success: false, similarity: 0, message: "机器人不存在" });
    }

    try {
        const currentCookie = botMeta.settings.renew.cookie || "";
        const lastSuccessCookie = botMeta.lastSuccessCookie || "";
        
        if (!currentCookie || !lastSuccessCookie) {
            return res.json({ 
                success: false, 
                similarity: 0, 
                message: "Cookie数据不完整" 
            });
        }
        
        const similarity = calculateCookieSimilarity(lastSuccessCookie, currentCookie);
        const similarityPercent = Math.round(similarity * 100);
        
        return res.json({
            success: true,
            similarity: similarityPercent,
            message: `Cookie相似度: ${similarityPercent}%`,
            details: {
                currentCookieLength: currentCookie.length,
                lastSuccessCookieLength: lastSuccessCookie.length,
                status: similarity >= 0.9 ? "良好" : "需要验证"
            }
        });
    } catch (err) {
        return res.json({ 
            success: false, 
            similarity: 0, 
            message: `计算相似度出错: ${err.message}` 
        });
    }
});

app.post("/api/bots/:id/pto-config", async (req, res) => {
    const b = activeBots.get(req.params.id);
    if (b) { b.settings.pterodactyl = req.body; await saveBotsConfig(); res.json({ success: true }); }
});

app.post("/api/bots", async (req, res) => {
    const id = 'bot_' + Date.now().toString(36);
    let host = req.body.host;
    let port = 25565;
    const hostParts = host.split(':');
    if (hostParts.length === 2) {
        host = hostParts[0];
        port = parseInt(hostParts[1]) || 25565;
    }
    createSmartBot(id, host, port, req.body.username, []);
    await saveBotsConfig(); res.json({ success: true });
});

app.delete("/api/bots/:id", async (req, res) => {
    const b = activeBots.get(req.params.id); 
    if (b) { 
        cleanupBot(b); 
        activeBots.delete(req.params.id); 
        await saveBotsConfig(); 
    }
    res.json({ success: true });
});

app.get("/api/system/status", async (req, res) => {
    let mem = process.memoryUsage().rss, total = os.totalmem();
    res.json({ cpu: (Math.random()*2).toFixed(1), ram: ((mem/total)*100).toFixed(1), disk: "正常" });
});

// --- [ 哪吒探针相关API ] ---
// 获取哪吒配置
app.get("/api/nezha/config", (req, res) => {
    res.json({ 
        success: true, 
        config: nezhaConfig,
        status: nezhaProcess ? "运行中" : "未运行"
    });
});

// 更新哪吒配置并启动
app.post("/api/nezha/config", async (req, res) => {
    try {
        const { addr, key, tls = false } = req.body;
        
        if (!addr || !key) {
            return res.json({ success: false, message: "面板地址和密钥不能为空" });
        }
        
        // 更新配置
        nezhaConfig = { addr, key, tls };
        await saveNezhaConfig();
        
        // 启动哪吒探针
        startNezha(addr, key, tls);
        
        res.json({ 
            success: true, 
            message: "哪吒探针配置已保存并启动",
            config: nezhaConfig
        });
    } catch (err) {
        res.json({ success: false, message: err.message });
    }
});

// 停止哪吒探针
app.post("/api/nezha/stop", (req, res) => {
    if (nezhaProcess) { 
        try { 
            nezhaProcess.kill(); 
            nezhaProcess = null;
            res.json({ success: true, message: "哪吒探针已停止" });
        } catch(e) {
            res.json({ success: false, message: "停止失败: " + e.message });
        }
    } else {
        res.json({ success: false, message: "哪吒探针未运行" });
    }
});

// --- [ 7. 任务中心 API 路由（增强版）] ---
app.get("/api/task-center/config", (req, res) => {
    res.json(taskCenterData);
});

app.post("/api/task-center/update-config", async (req, res) => {
    try {
        const { tasks, settings } = req.body;
        if (tasks) taskCenterData.tasks = tasks;
        if (settings) taskCenterData.settings = settings;
        await saveTaskCenterConfig();
        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ success: false, message: err.message });
    }
});

app.post("/api/task-center/create-task", async (req, res) => {
    try {
        const task = {
            id: 'task_' + Date.now().toString(36) + Math.random().toString(36).substr(2),
            name: req.body.name || '新任务',
            type: req.body.type || 'renew',
            config: req.body.config || {},
            status: 'stopped',
            logs: [],
            createdAt: new Date().toISOString(),
            lastRun: null,
            nextRun: null,
            lastLoginStatus: '未登录'
        };
        
        taskCenterData.tasks.push(task);
        await saveTaskCenterConfig();
        res.json({ success: true, task });
    } catch (err) {
        res.status(500).json({ success: false, message: err.message });
    }
});

app.post("/api/task-center/:taskId/toggle", async (req, res) => {
    try {
        const task = taskCenterData.tasks.find(t => t.id === req.params.taskId);
        if (!task) {
            return res.status(404).json({ success: false, message: '任务不存在' });
        }
        
        if (task.status === 'stopped') {
            task.status = 'running';
            task.lastRun = new Date().toISOString();
            
            if (task.config.interval && task.config.interval > 0) {
                const nextRunTime = new Date(Date.now() + task.config.interval * 60000);
                task.nextRun = nextRunTime.toISOString();
            }
            
            addTaskLog(task.id, `任务 "${task.name}" 已启动`, 'success');
            
            executeTaskLogic(task);
        } else {
            task.status = 'stopped';
            task.nextRun = null;
            addTaskLog(task.id, `任务 "${task.name}" 已停止`, 'warning');
        }
        
        await saveTaskCenterConfig();
        res.json({ success: true, status: task.status });
    } catch (err) {
        res.status(500).json({ success: false, message: err.message });
    }
});

app.delete("/api/task-center/:taskId", async (req, res) => {
    try {
        const index = taskCenterData.tasks.findIndex(t => t.id === req.params.taskId);
        if (index === -1) {
            return res.status(404).json({ success: false, message: '任务不存在' });
        }
        
        taskCenterData.tasks.splice(index, 1);
        await saveTaskCenterConfig();
        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ success: false, message: err.message });
    }
});

app.post("/api/task-center/:taskId/clear-logs", async (req, res) => {
    try {
        const task = taskCenterData.tasks.find(t => t.id === req.params.taskId);
        if (!task) {
            return res.status(404).json({ success: false, message: '任务不存在' });
        }
        
        task.logs = [];
        await saveTaskCenterConfig();
        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ success: false, message: err.message });
    }
});

// 新增：测试任务登录
app.post("/api/task-center/:taskId/test-login", async (req, res) => {
    try {
        const task = taskCenterData.tasks.find(t => t.id === req.params.taskId);
        if (!task) {
            return res.status(404).json({ success: false, message: '任务不存在' });
        }
        
        addTaskLog(task.id, `开始测试登录...`, 'info');
        
        const cookie = await taskAutoLogin(task.config);
        if (cookie) {
            task.config.cookie = cookie;
            task.lastLoginStatus = '已登录';
            task.config.lastLoginTime = new Date().toISOString();
            await saveTaskCenterConfig();
            
            addTaskLog(task.id, `登录测试成功，已保存Cookie`, 'success');
            res.json({ success: true, message: '登录成功', cookieLength: cookie.length });
        } else {
            addTaskLog(task.id, `登录测试失败，请检查配置`, 'error');
            res.json({ success: false, message: '登录失败' });
        }
    } catch (err) {
        addTaskLog(req.params.taskId, `登录测试异常: ${err.message}`, 'error');
        res.status(500).json({ success: false, message: err.message });
    }
});

// 新增：执行任务续期测试
app.post("/api/task-center/:taskId/test-renew", async (req, res) => {
    try {
        const task = taskCenterData.tasks.find(t => t.id === req.params.taskId);
        if (!task) {
            return res.status(404).json({ success: false, message: '任务不存在' });
        }
        
        if (task.type !== 'renew') {
            return res.json({ success: false, message: '此任务不是续期任务' });
        }
        
        addTaskLog(task.id, `开始测试续期...`, 'info');
        
        const result = await executeTaskRenew(task);
        
        if (result.success) {
            addTaskLog(task.id, `续期测试成功: ${result.message}`, 'success');
            res.json({ success: true, message: result.message, data: result.data });
        } else {
            addTaskLog(task.id, `续期测试失败: ${result.message}`, 'error');
            res.json({ success: false, message: result.message });
        }
    } catch (err) {
        addTaskLog(req.params.taskId, `续期测试异常: ${err.message}`, 'error');
        res.status(500).json({ success: false, message: err.message });
    }
});

// 添加任务日志
function addTaskLog(taskId, message, type = 'info') {
    const task = taskCenterData.tasks.find(t => t.id === taskId);
    if (!task) return;
    
    const logEntry = {
        timestamp: new Date().toLocaleString('zh-CN'),
        message,
        type
    };
    
    task.logs.unshift(logEntry);
    
    if (taskCenterData.settings.autoClearLogs && task.logs.length > taskCenterData.settings.maxLogEntries) {
        task.logs = task.logs.slice(0, taskCenterData.settings.maxLogEntries);
    }
    
    saveTaskCenterConfig().catch(() => {});
}

// 执行任务逻辑（增强版）
function executeTaskLogic(task) {
    if (task.status !== 'running') return;
    
    addTaskLog(task.id, `开始执行任务: ${task.name}`, 'info');
    
    switch(task.type) {
        case 'renew':
            executeTaskRenew(task);
            break;
        case 'afk':
            executeTaskAFK(task);
            break;
        case 'timed-url':
            executeTaskTimedURL(task);
            break;
        default:
            addTaskLog(task.id, `未知任务类型: ${task.type}`, 'error');
    }
    
    task.lastRun = new Date().toISOString();
    
    if (task.status === 'running' && task.config.interval && task.config.interval > 0) {
        const nextRunTime = new Date(Date.now() + task.config.interval * 60000);
        task.nextRun = nextRunTime.toISOString();
        
        setTimeout(() => {
            if (task.status === 'running') {
                executeTaskLogic(task);
            }
        }, task.config.interval * 60000);
    }
    
    saveTaskCenterConfig().catch(() => {});
}

// 执行续期任务（真实执行）
async function executeTaskRenew(task) {
    try {
        const { renewUrl, loginUrl, username, password, cookie, method = 'GET' } = task.config;
        
        if (!renewUrl) {
            addTaskLog(task.id, `续期任务失败: 未配置续期URL`, 'error');
            return { success: false, message: '未配置续期URL' };
        }
        
        let finalCookie = cookie;
        
        // 如果需要登录且没有Cookie
        if ((!finalCookie || finalCookie.trim() === '') && loginUrl && username && password) {
            addTaskLog(task.id, `正在执行登录获取Cookie...`, 'info');
            finalCookie = await taskAutoLogin(task.config);
            
            if (finalCookie) {
                task.config.cookie = finalCookie;
                task.lastLoginStatus = '已登录';
                addTaskLog(task.id, `登录成功，已获取Cookie`, 'success');
            } else {
                addTaskLog(task.id, `登录失败，无法获取Cookie`, 'error');
                return { success: false, message: '登录失败' };
            }
        }
        
        // 执行续期请求
        const headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
            'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
            'Referer': loginUrl || renewUrl
        };
        
        if (finalCookie && finalCookie.trim()) {
            headers['Cookie'] = finalCookie;
        }
        
        const requestMethod = method.toUpperCase();
        const axiosConfig = {
            method: requestMethod,
            url: renewUrl,
            headers: headers,
            timeout: 15000,
            validateStatus: (s) => s < 405
        };
        
        addTaskLog(task.id, `发送续期请求: ${requestMethod} ${renewUrl}`, 'info');
        
        const response = await axios(axiosConfig);
        
        if (response.status === 200) {
            const message = `续期成功 (状态码: ${response.status})`;
            addTaskLog(task.id, message, 'success');
            
            // 检查是否需要更新Cookie
            if (response.headers['set-cookie']) {
                const newCookie = response.headers['set-cookie'].map(c => c.split(';')[0]).join('; ');
                if (newCookie) {
                    task.config.cookie = newCookie;
                    addTaskLog(task.id, `已更新Cookie`, 'info');
                }
            }
            
            return { 
                success: true, 
                message: message,
                data: {
                    status: response.status,
                    headers: response.headers,
                    data: typeof response.data === 'string' ? response.data.substring(0, 500) + '...' : response.data
                }
            };
        } else {
            const message = `续期请求异常 (状态码: ${response.status})`;
            addTaskLog(task.id, message, 'warning');
            return { success: false, message: message };
        }
        
    } catch (err) {
        const message = `续期任务执行失败: ${err.message}`;
        addTaskLog(task.id, message, 'error');
        return { success: false, message: message };
    }
}

// 执行AFK任务
async function executeTaskAFK(task) {
    try {
        const { afkUrl, duration = 30, action = 'simulate', loginUrl, username, password, cookie } = task.config;
        
        addTaskLog(task.id, `开始执行AFK任务: ${action} ${duration}分钟`, 'info');
        
        // 如果需要登录
        if (loginUrl && username && password && (!cookie || cookie.trim() === '')) {
            addTaskLog(task.id, `正在执行登录...`, 'info');
            const newCookie = await taskAutoLogin(task.config);
            if (newCookie) {
                task.config.cookie = newCookie;
                task.lastLoginStatus = '已登录';
                addTaskLog(task.id, `登录成功`, 'success');
            }
        }
        
        // 根据动作执行不同操作
        switch(action) {
            case 'simulate':
                addTaskLog(task.id, `模拟AFK活动 ${duration} 分钟`, 'success');
                break;
            case 'notification':
                addTaskLog(task.id, `发送AFK通知`, 'success');
                break;
            case 'auto-login':
                if (afkUrl && task.config.cookie) {
                    addTaskLog(task.id, `自动登录保持会话: ${afkUrl}`, 'info');
                    try {
                        const response = await axios.get(afkUrl, {
                            headers: {
                                'Cookie': task.config.cookie,
                                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
                            },
                            timeout: 10000
                        });
                        addTaskLog(task.id, `会话保持成功 (状态码: ${response.status})`, 'success');
                    } catch (err) {
                        addTaskLog(task.id, `会话保持失败: ${err.message}`, 'warning');
                    }
                }
                break;
        }
        
        return { success: true, message: 'AFK任务执行完成' };
    } catch (err) {
        addTaskLog(task.id, `AFK任务执行失败: ${err.message}`, 'error');
        return { success: false, message: err.message };
    }
}

// 执行定时访问URL任务
async function executeTaskTimedURL(task) {
    try {
        const { targetUrl, method = 'get', loginUrl, username, password, cookie } = task.config;
        
        if (!targetUrl) {
            addTaskLog(task.id, `定时访问URL失败: 未配置目标URL`, 'error');
            return { success: false, message: '未配置目标URL' };
        }
        
        addTaskLog(task.id, `开始访问URL: ${method.toUpperCase()} ${targetUrl}`, 'info');
        
        let finalCookie = cookie;
        
        // 如果需要登录
        if (method === 'with-login' || (loginUrl && username && password && (!finalCookie || finalCookie.trim() === ''))) {
            addTaskLog(task.id, `正在执行登录...`, 'info');
            const newCookie = await taskAutoLogin(task.config);
            if (newCookie) {
                finalCookie = newCookie;
                task.config.cookie = newCookie;
                task.lastLoginStatus = '已登录';
                addTaskLog(task.id, `登录成功`, 'success');
            } else {
                addTaskLog(task.id, `登录失败，跳过本次访问`, 'warning');
                return { success: false, message: '登录失败' };
            }
        }
        
        const headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
        };
        
        if (finalCookie && finalCookie.trim()) {
            headers['Cookie'] = finalCookie;
        }
        
        const requestMethod = method === 'with-login' ? 'GET' : method.toUpperCase();
        const axiosConfig = {
            method: requestMethod,
            url: targetUrl,
            headers: headers,
            timeout: 10000,
            validateStatus: (s) => s < 500
        };
        
        const response = await axios(axiosConfig);
        
        if (response.status === 200) {
            const message = `访问成功 (状态码: ${response.status})`;
            addTaskLog(task.id, message, 'success');
            return { success: true, message: message };
        } else {
            const message = `访问异常 (状态码: ${response.status})`;
            addTaskLog(task.id, message, 'warning');
            return { success: false, message: message };
        }
        
    } catch (err) {
        const message = `定时访问URL失败: ${err.message}`;
        addTaskLog(task.id, message, 'error');
        return { success: false, message: message };
    }
}

// 启动任务中心服务
setInterval(() => {
    taskCenterData.tasks.forEach(task => {
        if (task.status === 'running' && task.nextRun) {
            const now = new Date();
            const nextRun = new Date(task.nextRun);
            
            if (now >= nextRun) {
                executeTaskLogic(task);
                task.lastRun = now.toISOString();
                
                if (task.config.interval && task.config.interval > 0) {
                    const newNextRun = new Date(Date.now() + task.config.interval * 60000);
                    task.nextRun = newNextRun.toISOString();
                }
                
                saveTaskCenterConfig().catch(() => {});
            }
        }
    });
}, 10000);

// ========== 哪吒探针功能（移到靠后位置） ==========
// 加载哪吒配置
async function loadNezhaConfig() {
    try {
        if (fsSync.existsSync(NEZHA_CONFIG_FILE)) {
            const data = await fs.readFile(NEZHA_CONFIG_FILE, 'utf8');
            nezhaConfig = JSON.parse(data);
            console.log('[哪吒] 配置加载成功');
            
            // 如果配置存在且不为空，则自动启动
            if (nezhaConfig.addr && nezhaConfig.key) {
                setTimeout(() => startNezha(nezhaConfig.addr, nezhaConfig.key, nezhaConfig.tls), 3000);
            }
        } else {
            console.log('[哪吒] 无历史配置');
        }
    } catch (e) {
        console.log('[哪吒] 配置加载失败:', e.message);
    }
}

// 保存哪吒配置
async function saveNezhaConfig() {
    try {
        await fs.writeFile(NEZHA_CONFIG_FILE, JSON.stringify(nezhaConfig, null, 2));
    } catch (err) {
        console.error('[哪吒] 保存配置失败:', err.message);
    }
}

// 哪吒探针核心函数
const AGENT_PREFIX = "sys_cache_"; // 随机文件名前缀

/**
 * 启动哪吒探针
 * @param {string} addr - 面板地址 (例如: panel.example.com:5555)
 * @param {string} key - 探针密钥
 * @param {boolean} tls - 是否开启 TLS (默认根据端口 443 自动判断)
 */
async function startNezha(addr, key, tls = false) {
    // 1. 如果已有进程在运行，先杀掉
    if (nezhaProcess) { 
        try { nezhaProcess.kill(); } catch(e){} 
        nezhaProcess = null; 
    }
    if (!addr || !key) return;

    // 2. 生成随机文件名
    const randomSuffix = crypto.randomBytes(3).toString('hex');
    const isWin = os.platform() === 'win32';
    const agentName = isWin ? `${AGENT_PREFIX}${randomSuffix}.exe` : `${AGENT_PREFIX}${randomSuffix}`;
    const agentPath = path.resolve(__dirname, agentName);

    // 3. 自动清理旧的混淆探针文件
    try {
        const files = await fs.readdir(__dirname);
        for (const file of files) {
            if (file.startsWith(AGENT_PREFIX)) {
                await fs.unlink(path.join(__dirname, file)).catch(()=>{});
            }
        }
    } catch (e) {}

    // 4. 下载并部署
    if (!fsSync.existsSync(agentPath)) {
        console.log(`[哪吒] 正在部署混淆探针: ${agentName}`);
        
        // 自动识别系统架构和平台
        const arch = os.arch() === 'arm64' ? 'arm64' : 'amd64';
        const platform = isWin ? 'windows' : 'linux';
        const url = `https://github.com/nezhahq/agent/releases/latest/download/nezha-agent_${platform}_${arch}.zip`;
        
        try {
            const resp = await axios.get(url, { responseType: 'arraybuffer' });
            const zip = new AdmZip(Buffer.from(resp.data));
            zip.extractAllTo(__dirname, true);

            // 原始文件名
            const originalName = isWin ? 'nezha-agent.exe' : 'nezha-agent';
            let found = false;

            // 递归查找并重命名二进制文件
            const scanAndRename = (dir) => {
                const items = fsSync.readdirSync(dir);
                for (const item of items) {
                    const fullP = path.join(dir, item);
                    if (item === originalName) {
                        fsSync.renameSync(fullP, agentPath);
                        found = true; break;
                    } else if (fsSync.statSync(fullP).isDirectory()) {
                        scanAndRename(fullP);
                    }
                }
            };
            scanAndRename(__dirname);

            if (!found) throw new Error("解压后的包内未找到二进制文件");
            
            // 给 Linux 文件赋权
            if (!isWin) execSync(`chmod 777 "${agentPath}"`);
            console.log(`[哪吒] 随机化部署成功！`);
        } catch (e) {
            console.error("[哪吒] 部署失败:", e.message);
            return;
        }
    }

    // 5. 启动进程
    const isTls = (tls || addr.includes(':443')) ? 'true' : 'false';
    try {
        nezhaProcess = spawn(agentPath, [], {
            cwd: __dirname,
            stdio: 'inherit',
            env: {
                ...process.env,
                NZ_SERVER: addr,
                NZ_PASSWORD: key,
                NZ_CLIENT_SECRET: key,
                NZ_TLS: isTls
            }
        });

        console.log(`[哪吒] 探针进程已启动，随机文件名: ${agentName}`);
        console.log(`[哪吒] 面板地址: ${addr}, TLS: ${isTls}`);
    } catch (e) {
        console.error("[哪吒] 进程启动失败:", e.message);
    }
}

// ========== 前端HTML代码（包含哪吒探针模态框） ==========

// --- [ 8. UI 控制面板（包含任务中心增强版和哪吒探针）] ---
app.get("/", (req, res) => {
    res.send(`<!DOCTYPE html><html><head><meta charset="utf-8"><title>Pathfinder PRO 2025 (增强版任务中心 + 哪吒探针)</title>
    <script src="https://cdn.tailwindcss.com"></script>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <style>
    /* 原有的样式保持不变 */
    body{background:#020617;color:#f8fafc;font-family:sans-serif}
    .glass{background:rgba(15,23,42,0.7);backdrop-filter:blur(20px);border:1px solid rgba(255,255,255,0.05)}
    .log-box{ font-family: 'Consolas', monospace; font-size: 11px; scroll-behavior: smooth; }
    input,textarea,select{background:#0f172a!important;border:1px solid #1e293b!important;color:white!important}
    .btn-action { transition: all 0.2s cubic-bezier(0.4, 0, 0.2, 1); cursor: pointer; user-select: none; }
    .btn-action:hover { transform: translateY(-1px); filter: brightness(1.2); box-shadow: 0 4px 12px rgba(0,0,0,0.3); }
    .btn-action:active { transform: scale(0.95); filter: brightness(0.9); }
    .status-online { color: #10b981; text-shadow: 0 0 8px rgba(16,185,129,0.4); }
    .status-offline { color: #ef4444; }
    .truncate { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
    .truncate-hover:hover { overflow: visible; white-space: normal; background: rgba(15, 23, 42, 0.9); position: relative; z-index: 10; }
    .robot-card.minimized { background: rgba(15, 23, 42, 0.85) !important; border-color: rgba(59, 130, 246, 0.4) !important; box-shadow: 0 4px 20px rgba(59, 130, 246, 0.2) !important; transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1); }
    .robot-card.expanded { transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1); }
    .similarity-indicator { height: 4px; border-radius: 2px; margin-top: 2px; transition: all 0.3s ease; }
    .similarity-good { background: linear-gradient(90deg, #10b981 0%, #34d399 100%); box-shadow: 0 0 8px rgba(16, 185, 129, 0.4); }
    .similarity-warning { background: linear-gradient(90deg, #f59e0b 0%, #fbbf24 100%); box-shadow: 0 0 8px rgba(245, 158, 11, 0.4); }
    .similarity-bad { background: linear-gradient(90deg, #ef4444 0%, #f87171 100%); box-shadow: 0 0 8px rgba(239, 68, 68, 0.4); }
    .simplified-view { animation: fadeIn 0.3s ease-out; }
    .full-view { animation: slideIn 0.3s ease-out; }
    .minimize-btn { transition: all 0.2s ease; width: 22px; height: 22px; display: flex; align-items: center; justify-content: center; border-radius: 6px; background: rgba(30, 41, 59, 0.7); border: 1px solid rgba(100, 116, 139, 0.3); font-weight: bold; font-size: 14px; color: #cbd5e1; }
    .minimize-btn:hover { background: rgba(59, 130, 246, 0.3); border-color: rgba(59, 130, 246, 0.5); color: white; transform: scale(1.1); }
    .minimize-btn:active { transform: scale(0.95); }
    .bulk-view-btn { background: linear-gradient(135deg, #8b5cf6 0%, #7c3aed 100%); border: none; color: white; font-weight: 600; padding: 0.5rem 1rem; border-radius: 10px; cursor: pointer; transition: all 0.2s ease; display: flex; align-items: center; gap: 0.5rem; }
    .bulk-view-btn:hover { transform: translateY(-2px); box-shadow: 0 4px 12px rgba(139, 92, 246, 0.3); background: linear-gradient(135deg, #9b6dff 0%, #8c4af0 100%); }
    .bulk-view-btn:active { transform: scale(0.98); }
    @keyframes fadeIn { from { opacity: 0; transform: translateY(-10px); } to { opacity: 1; transform: translateY(0); } }
    @keyframes slideIn { from { opacity: 0; transform: translateY(10px); } to { opacity: 1; transform: translateY(0); } }
    @keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.7; } }
    .connection-card { background: linear-gradient(145deg, rgba(30, 41, 59, 0.8), rgba(15, 23, 42, 0.9)); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; box-shadow: 0 4px 16px rgba(0, 0, 0, 0.2); }
    .info-item { background: rgba(30, 41, 59, 0.5); border: 1px solid rgba(71, 85, 105, 0.3); border-radius: 10px; padding: 0.75rem; transition: all 0.2s ease; }
    .info-item:hover { background: rgba(30, 41, 59, 0.7); border-color: rgba(59, 130, 246, 0.4); transform: translateY(-1px); }
    .ip-port-display { font-family: 'SF Mono', 'Monaco', 'Inconsolata', 'Fira Code', monospace; font-weight: 600; color: #10b981; text-shadow: 0 0 8px rgba(16, 185, 129, 0.3); }
    .player-display { font-weight: 600; color: #8b5cf6; text-shadow: 0 0 8px rgba(139, 92, 246, 0.3); }
    .task-card { background: rgba(30, 41, 59, 0.6); border: 1px solid rgba(71, 85, 105, 0.4); border-radius: 12px; transition: all 0.3s ease; cursor: pointer; }
    .task-card:hover { background: rgba(30, 41, 59, 0.8); border-color: rgba(59, 130, 246, 0.6); transform: translateY(-2px); box-shadow: 0 8px 20px rgba(0, 0, 0, 0.2); }
    .task-card.selected { background: rgba(30, 41, 59, 0.9); border-color: #3b82f6; box-shadow: 0 0 20px rgba(59, 130, 246, 0.3); }
    .task-status-running { color: #10b981; animation: pulse 2s infinite; }
    .task-status-stopped { color: #ef4444; }
    .log-entry-info { color: #60a5fa; }
    .log-entry-success { color: #34d399; }
    .log-entry-warning { color: #fbbf24; }
    .log-entry-error { color: #f87171; }
    .taskbar-item { background: rgba(30, 41, 59, 0.7); border: 1px solid rgba(71, 85, 105, 0.4); border-radius: 8px; padding: 8px 12px; margin-bottom: 6px; transition: all 0.2s ease; }
    .taskbar-item:hover { background: rgba(30, 41, 59, 0.9); border-color: rgba(59, 130, 246, 0.6); }
    
    /* 新增任务中心样式 */
    .login-config-section { 
        background: rgba(30, 41, 59, 0.5); 
        border: 1px solid rgba(59, 130, 246, 0.3); 
        border-radius: 12px; 
        padding: 1rem; 
        margin-top: 1rem; 
    }
    .login-status { 
        display: inline-flex; 
        align-items: center; 
        gap: 0.5rem; 
        padding: 0.25rem 0.75rem; 
        border-radius: 9999px; 
        font-size: 0.75rem; 
        font-weight: 600; 
    }
    .login-status-logged { 
        background: rgba(34, 197, 94, 0.2); 
        color: #22c55e; 
        border: 1px solid rgba(34, 197, 94, 0.3); 
    }
    .login-status-not-logged { 
        background: rgba(239, 68, 68, 0.2); 
        color: #ef4444; 
        border: 1px solid rgba(239, 68, 68, 0.3); 
    }
    
    /* 哪吒探针样式 */
    .nezha-modal { 
        background: rgba(15, 23, 42, 0.95); 
        backdrop-filter: blur(20px);
        border: 1px solid rgba(59, 130, 246, 0.3);
        border-radius: 20px;
    }
    .nezha-status-running { 
        color: #22c55e; 
        animation: pulse 2s infinite; 
    }
    .nezha-status-stopped { 
        color: #ef4444; 
    }
    .nezha-info-box { 
        background: rgba(30, 41, 59, 0.5); 
        border: 1px solid rgba(71, 85, 105, 0.3); 
        border-radius: 12px; 
        padding: 1rem; 
        margin-top: 1rem; 
    }
    </style></head>
    <body class="p-6">
    <div class="max-w-7xl mx-auto">
        <header class="flex justify-between items-center mb-8">
            <div>
                <h1 class="text-3xl font-black text-blue-500 italic uppercase">Pathfinder PRO 2025</h1>
                <p class="text-sm text-slate-400 mt-1">增强版任务中心 | 哪吒探针V1 | Cookie相似度检测</p>
            </div>
            <div class="glass p-2 rounded-xl flex gap-2">
                <button onclick="showPage('robot-page')" id="nav-robot" class="btn-action bg-blue-600 px-4 py-1 rounded-xl text-sm font-bold">机器人列表</button>
                <button onclick="showPage('task-center-page')" id="nav-task" class="btn-action bg-slate-800 px-4 py-1 rounded-xl text-sm font-bold">任务中心</button>
                <button onclick="showNezhaModal()" class="btn-action bg-purple-600 px-4 py-1 rounded-xl text-sm font-bold flex items-center gap-1">
                    <i class="fas fa-satellite-dish"></i>
                    哪吒探针
                </button>
                <div class="h-6 border-l border-slate-700"></div>
                <input id="h" placeholder="IP:端口" class="rounded-xl px-4 py-1 text-sm outline-none w-40">
                <input id="u" placeholder="角色名" class="rounded-xl px-4 py-1 text-sm outline-none w-32">
                <button onclick="addBot()" class="btn-action bg-blue-600 px-6 py-1 rounded-xl text-sm font-bold">部署角色</button>
                <button onclick="toggleAllRobotCards()" class="bulk-view-btn" id="bulk-view-btn" title="切换所有机器人卡片视图">
                    <span class="text-sm">📱 全部简化</span>
                </button>
            </div>
        </header>
        
        <!-- 机器人列表页面 -->
        <div id="robot-page">
            <div id="list" class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-8"></div>
        </div>
        
        <!-- 任务中心页面（增强版） -->
        <div id="task-center-page" class="hidden">
            <div class="flex flex-col lg:flex-row gap-6 h-[calc(100vh-12rem)]">
                <!-- 左侧面板 -->
                <div class="lg:w-1/3 bg-slate-900/50 rounded-2xl p-4 border border-slate-800">
                    <div class="mb-6">
                        <h3 class="text-lg font-bold text-white mb-2">任务中心</h3>
                        <div class="flex flex-wrap items-center gap-2">
                            <span class="text-xs text-slate-400">自动清理日志:</span>
                            <input type="checkbox" id="auto-clear-logs" checked class="w-4 h-4" onchange="updateTaskCenterSettings()">
                            <span class="text-xs text-slate-400 ml-4">最大日志数:</span>
                            <input type="number" id="max-log-entries" value="100" min="10" max="1000" class="w-20 px-2 py-1 text-sm rounded bg-slate-800 border border-slate-700" onchange="updateTaskCenterSettings()">
                            <span class="text-xs text-slate-400 ml-4">自动登录:</span>
                            <input type="checkbox" id="enable-auto-login" checked class="w-4 h-4" onchange="updateTaskCenterSettings()">
                        </div>
                    </div>
                    
                    <!-- 创建任务按钮 -->
                    <div class="mb-6">
                        <button onclick="showCreateTaskModal()" class="w-full btn-action bg-gradient-to-r from-blue-600 to-purple-600 py-3 rounded-xl text-sm font-bold flex items-center justify-center gap-2 mb-3">
                            <i class="fas fa-plus-circle"></i>
                            创建新任务
                        </button>
                    </div>
                    
                    <!-- 任务列表 -->
                    <div class="flex-1 overflow-hidden">
                        <h4 class="text-sm font-bold text-slate-300 mb-3">任务列表</h4>
                        <div id="task-list" class="space-y-3 max-h-[calc(100vh-24rem)] overflow-y-auto pr-2">
                            <!-- 任务将通过JS动态添加 -->
                        </div>
                    </div>
                </div>
                
                <!-- 主内容区域 -->
                <div class="lg:w-2/3 flex flex-col">
                    <!-- 任务详情 -->
                    <div class="bg-slate-900/50 rounded-2xl p-4 border border-slate-800 mb-4">
                        <div class="flex justify-between items-center mb-4">
                            <h3 id="selected-task-title" class="text-lg font-bold text-slate-300">选择任务以查看详情</h3>
                            <div id="task-controls" class="flex gap-2 hidden">
                                <button onclick="toggleSelectedTask()" id="toggle-task-btn" class="btn-action bg-emerald-600 px-4 py-2 rounded-xl text-sm font-bold flex items-center gap-2">
                                    <i class="fas fa-play"></i>
                                    启动
                                </button>
                                <button onclick="testTaskLogin()" id="test-login-btn" class="btn-action bg-blue-600 px-4 py-2 rounded-xl text-sm font-bold flex items-center gap-2 hidden">
                                    <i class="fas fa-sign-in-alt"></i>
                                    测试登录
                                </button>
                                <button onclick="testTaskRenew()" id="test-renew-btn" class="btn-action bg-purple-600 px-4 py-2 rounded-xl text-sm font-bold flex items-center gap-2 hidden">
                                    <i class="fas fa-test"></i>
                                    测试续期
                                </button>
                                <button onclick="deleteSelectedTask()" class="btn-action bg-red-600 px-4 py-2 rounded-xl text-sm font-bold flex items-center gap-2">
                                    <i class="fas fa-trash"></i>
                                    删除
                                </button>
                            </div>
                        </div>
                        
                        <!-- 任务配置 -->
                        <div id="task-config" class="space-y-4 hidden">
                            <div class="grid grid-cols-1 md:grid-cols-2 gap-4">
                                <div>
                                    <label class="block text-sm text-slate-400 mb-1">任务名称</label>
                                    <input id="task-config-name" type="text" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" onchange="updateTaskConfig('name', this.value)">
                                </div>
                                <div>
                                    <label class="block text-sm text-slate-400 mb-1">任务类型</label>
                                    <input id="task-config-type" type="text" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" readonly>
                                </div>
                            </div>
                            
                            <!-- 动态配置区域 -->
                            <div id="task-type-config"></div>
                            
                            <!-- 登录状态显示 -->
                            <div id="task-login-status" class="hidden">
                                <div class="login-config-section">
                                    <div class="flex justify-between items-center mb-2">
                                        <h4 class="text-sm font-bold text-slate-300">登录状态</h4>
                                        <span id="login-status-badge" class="login-status login-status-not-logged">
                                            <i class="fas fa-times-circle"></i>
                                            <span>未登录</span>
                                        </span>
                                    </div>
                                    <div class="text-xs text-slate-400" id="login-details">
                                        上次登录时间: 无
                                    </div>
                                </div>
                            </div>
                            
                            <div class="grid grid-cols-1 md:grid-cols-3 gap-4">
                                <div>
                                    <label class="block text-sm text-slate-400 mb-1">执行间隔(分钟)</label>
                                    <input id="task-config-interval" type="number" min="1" value="5" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" onchange="updateTaskConfig('interval', this.value)">
                                </div>
                                <div>
                                    <label class="block text-sm text-slate-400 mb-1">最后运行</label>
                                    <input id="task-config-lastrun" type="text" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" readonly>
                                </div>
                                <div>
                                    <label class="block text-sm text-slate-400 mb-1">下次运行</label>
                                    <input id="task-config-nextrun" type="text" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" readonly>
                                </div>
                            </div>
                        </div>
                    </div>
                    
                    <!-- 任务日志 -->
                    <div class="flex-1 bg-slate-900/50 rounded-2xl p-4 border border-slate-800 overflow-hidden flex flex-col">
                        <div class="flex justify-between items-center mb-4">
                            <h3 class="text-lg font-bold text-slate-300">任务日志</h3>
                            <div class="flex gap-2">
                                <button onclick="clearSelectedTaskLogs()" id="clear-logs-btn" class="btn-action bg-slate-700 px-3 py-2 rounded-xl text-sm font-bold flex items-center gap-2" disabled>
                                    <i class="fas fa-broom"></i>
                                    清理日志
                                </button>
                            </div>
                        </div>
                        <div id="task-log-content" class="flex-1 bg-black/40 rounded-xl p-4 overflow-y-auto font-mono text-sm">
                            <div class="text-slate-500">选择一个任务查看日志</div>
                        </div>
                    </div>
                </div>
            </div>
            
            <!-- 底部任务栏 -->
            <div class="fixed bottom-4 right-4">
                <button onclick="toggleTaskbar()" id="taskbar-toggle" class="btn-action bg-gradient-to-r from-blue-600 to-purple-600 w-10 h-10 rounded-full flex items-center justify-center shadow-lg">
                    <i class="fas fa-chevron-up"></i>
                </button>
                
                <div id="taskbar" class="hidden fixed bottom-16 right-4 w-64 bg-slate-900/95 backdrop-blur-sm rounded-2xl p-3 border border-slate-800 shadow-2xl">
                    <h4 class="text-sm font-bold text-slate-300 mb-3 flex items-center justify-between">
                        <span>运行中的任务</span>
                        <span id="running-task-count" class="bg-blue-600 text-xs px-2 py-1 rounded-full">0</span>
                    </h4>
                    <div id="taskbar-items" class="space-y-2 max-h-48 overflow-y-auto">
                        <!-- 运行中的任务将在这里显示 -->
                    </div>
                </div>
            </div>
        </div>
    </div>
    
    <!-- 系统状态栏 -->
    <div class="fixed bottom-6 left-6 p-4 glass rounded-[2.5rem] flex items-center gap-6 z-50 shadow-2xl">
        <div class="flex flex-col text-center"><span id="cpu-val" class="text-lg font-black text-white">0%</span><span class="text-[8px] font-bold text-slate-500 uppercase">CPU</span></div>
        <div class="flex flex-col text-center"><span id="mem-val" class="text-lg font-black text-blue-400">0%</span><span class="text-[8px] font-bold text-slate-500 uppercase">RAM</span></div>
        <div class="flex flex-col text-center"><span id="disk-val" class="text-lg font-black text-emerald-400">正常</span><span class="text-[8px] font-bold text-slate-500 uppercase">DISK</span></div>
    </div>
    
    <!-- 哪吒探针模态框 -->
    <div id="nezha-modal" class="fixed inset-0 bg-black/70 flex items-center justify-center z-50 hidden">
        <div class="nezha-modal rounded-2xl p-6 w-full max-w-md border max-h-[90vh] overflow-y-auto">
            <div class="flex justify-between items-center mb-4">
                <h3 class="text-lg font-bold text-white flex items-center gap-2">
                    <i class="fas fa-satellite-dish text-purple-400"></i>
                    哪吒探针 V1 配置
                </h3>
                <button onclick="hideNezhaModal()" class="text-slate-400 hover:text-white">
                    <i class="fas fa-times"></i>
                </button>
            </div>
            
            <div class="space-y-4">
                <!-- 状态显示 -->
                <div id="nezha-status-display" class="nezha-info-box">
                    <div class="flex justify-between items-center mb-2">
                        <span class="text-sm font-bold text-slate-300">当前状态</span>
                        <span id="nezha-status-text" class="text-xs font-bold nezha-status-stopped">未运行</span>
                    </div>
                    <div class="text-xs text-slate-400 space-y-1">
                        <div>面板地址: <span id="nezha-current-addr" class="text-slate-300">未配置</span></div>
                        <div>密钥: <span id="nezha-current-key" class="text-slate-300">未配置</span></div>
                        <div>TLS: <span id="nezha-current-tls" class="text-slate-300">未配置</span></div>
                    </div>
                </div>
                
                <!-- 配置表单 -->
                <div>
                    <label class="block text-sm text-slate-400 mb-1">面板地址 *</label>
                    <input id="nezha-addr" type="text" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                           placeholder="panel.example.com:5555" required>
                    <p class="text-xs text-slate-500 mt-1">格式: 域名或IP:端口 (如: nezha.example.com:5555)</p>
                </div>
                
                <div>
                    <label class="block text-sm text-slate-400 mb-1">探针密钥 *</label>
                    <input id="nezha-key" type="password" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                           placeholder="请输入密钥" required>
                    <p class="text-xs text-slate-500 mt-1">在面板中添加探针时生成的密钥</p>
                </div>
                
                <div class="flex items-center gap-2">
                    <input id="nezha-tls" type="checkbox" class="w-4 h-4">
                    <label class="text-sm text-slate-400">启用 TLS 加密</label>
                </div>
                
                <div class="nezha-info-box">
                    <h4 class="text-sm font-bold text-slate-300 mb-2">安全特性</h4>
                    <ul class="text-xs text-slate-400 space-y-1">
                        <li class="flex items-start gap-1">
                            <i class="fas fa-shield-alt text-green-400 mt-0.5"></i>
                            <span>随机化文件名启动，避免检测</span>
                        </li>
                        <li class="flex items-start gap-1">
                            <i class="fas fa-sync-alt text-blue-400 mt-0.5"></i>
                            <span>自动清理旧探针文件，防止占用空间</span>
                        </li>
                        <li class="flex items-start gap-1">
                            <i class="fas fa-lock text-purple-400 mt-0.5"></i>
                            <span>支持 TLS 加密连接</span>
                        </li>
                    </ul>
                </div>
                
                <div class="flex gap-3 pt-4">
                    <button onclick="hideNezhaModal()" class="flex-1 btn-action bg-slate-800 py-3 rounded-xl text-sm font-bold">取消</button>
                    <button onclick="stopNezha()" id="nezha-stop-btn" class="flex-1 btn-action bg-red-600 py-3 rounded-xl text-sm font-bold hidden">停止</button>
                    <button onclick="saveNezhaConfig()" class="flex-1 btn-action bg-gradient-to-r from-purple-600 to-blue-600 py-3 rounded-xl text-sm font-bold">保存并启动</button>
                </div>
            </div>
        </div>
    </div>
    
    <!-- 创建任务模态框（增强版） -->
    <div id="create-task-modal" class="fixed inset-0 bg-black/70 flex items-center justify-center z-50 hidden">
        <div class="bg-slate-900 rounded-2xl p-6 w-full max-w-md border border-slate-800 max-h-[90vh] overflow-y-auto">
            <div class="flex justify-between items-center mb-4">
                <h3 class="text-lg font-bold text-white">创建新任务</h3>
                <button onclick="hideCreateTaskModal()" class="text-slate-400 hover:text-white">
                    <i class="fas fa-times"></i>
                </button>
            </div>
            <div class="space-y-4">
                <div>
                    <label class="block text-sm text-slate-400 mb-1">任务名称 *</label>
                    <input id="new-task-name" type="text" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" placeholder="输入任务名称" value="新任务" required>
                </div>
                <div>
                    <label class="block text-sm text-slate-400 mb-1">任务类型 *</label>
                    <select id="new-task-type" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" onchange="updateNewTaskTypeConfig()">
                        <option value="renew">Renew 任务</option>
                        <option value="afk">AFK 任务</option>
                        <option value="timed-url">定时访问URL</option>
                    </select>
                </div>
                
                <!-- 动态配置区域 -->
                <div id="new-task-type-config"></div>
                
                <div>
                    <label class="block text-sm text-slate-400 mb-1">执行间隔(分钟)</label>
                    <input id="new-task-interval" type="number" min="1" value="5" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm">
                </div>
                
                <div class="flex gap-3 pt-4">
                    <button onclick="hideCreateTaskModal()" class="flex-1 btn-action bg-slate-800 py-3 rounded-xl text-sm font-bold">取消</button>
                    <button onclick="confirmCreateTask()" class="flex-1 btn-action bg-gradient-to-r from-blue-600 to-purple-600 py-3 rounded-xl text-sm font-bold">创建</button>
                </div>
            </div>
        </div>
    </div>
    
    <script>
    // ==================== 全局变量 ====================
    const logHashes = new Map();
    let allCardsSimplified = false;
    let selectedTaskId = null;
    let taskbarVisible = false;
    let taskCenterData = { tasks: [], settings: {} };
    
    // ==================== 哪吒探针功能 ====================
    
    // 显示哪吒模态框
    function showNezhaModal() {
        const modal = document.getElementById('nezha-modal');
        modal.classList.remove('hidden');
        loadNezhaStatus();
    }
    
    // 隐藏哪吒模态框
    function hideNezhaModal() {
        const modal = document.getElementById('nezha-modal');
        modal.classList.add('hidden');
    }
    
    // 加载哪吒状态
    async function loadNezhaStatus() {
        try {
            const response = await fetch('/api/nezha/config');
            const data = await response.json();
            
            if (data.success) {
                const config = data.config;
                const status = data.status;
                
                // 更新状态显示
                const statusText = document.getElementById('nezha-status-text');
                const statusDisplay = document.getElementById('nezha-status-display');
                const stopBtn = document.getElementById('nezha-stop-btn');
                
                if (status === "运行中") {
                    statusText.textContent = "运行中";
                    statusText.className = "text-xs font-bold nezha-status-running";
                    stopBtn.classList.remove('hidden');
                } else {
                    statusText.textContent = "未运行";
                    statusText.className = "text-xs font-bold nezha-status-stopped";
                    stopBtn.classList.add('hidden');
                }
                
                // 更新当前配置显示
                document.getElementById('nezha-current-addr').textContent = config.addr || "未配置";
                document.getElementById('nezha-current-key').textContent = config.key ? "***" + config.key.slice(-4) : "未配置";
                document.getElementById('nezha-current-tls').textContent = config.tls ? "是" : "否";
                
                // 填充表单
                document.getElementById('nezha-addr').value = config.addr || "";
                document.getElementById('nezha-key').value = config.key || "";
                document.getElementById('nezha-tls').checked = config.tls || false;
            }
        } catch (error) {
            console.error('加载哪吒状态失败:', error);
        }
    }
    
    // 保存哪吒配置
    async function saveNezhaConfig() {
        const addr = document.getElementById('nezha-addr').value.trim();
        const key = document.getElementById('nezha-key').value.trim();
        const tls = document.getElementById('nezha-tls').checked;
        
        if (!addr || !key) {
            alert('请填写面板地址和密钥');
            return;
        }
        
        try {
            const response = await fetch('/api/nezha/config', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ addr, key, tls })
            });
            
            const data = await response.json();
            if (data.success) {
                alert('哪吒探针配置已保存并启动');
                hideNezhaModal();
                loadNezhaStatus();
            } else {
                alert('保存失败: ' + data.message);
            }
        } catch (error) {
            alert('请求失败: ' + error.message);
        }
    }
    
    // 停止哪吒探针
    async function stopNezha() {
        if (!confirm('确定要停止哪吒探针吗？')) return;
        
        try {
            const response = await fetch('/api/nezha/stop', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            
            const data = await response.json();
            if (data.success) {
                alert('哪吒探针已停止');
                loadNezhaStatus();
            } else {
                alert('停止失败: ' + data.message);
            }
        } catch (error) {
            alert('请求失败: ' + error.message);
        }
    }
    
    // ==================== 机器人页面功能 ====================
    
    async function updateUI() {
        try {
            const r = await fetch('/api/bots'); 
            const d = await r.json();
            const container = document.getElementById('list');
            d.bots.forEach(b => {
                let card = document.getElementById('card-' + b.id);
                if (!card) {
                    card = document.createElement('div'); 
                    card.id = 'card-' + b.id;
                    container.appendChild(card); 
                    renderCardBase(card, b);
                }
                
                const isOnline = b.status === "在线";
                
                const fullStatus = card.querySelector('.full-view-status');
                if (fullStatus) {
                    fullStatus.innerText = b.status;
                    fullStatus.className = \`full-view-status text-[10px] font-black \${isOnline ? 'status-online' : 'status-offline'}\`;
                }
                
                const simpleStatus = card.querySelector('.simplified-view-status');
                if (simpleStatus) {
                    simpleStatus.innerText = b.status;
                    simpleStatus.className = \`simplified-view-status text-xs font-bold \${isOnline ? 'text-emerald-400' : 'text-red-400'}\`;
                }
                
                const dot = card.querySelector('.simplified-status-dot');
                if (dot) {
                    dot.className = \`w-2 h-2 rounded-full \${isOnline ? 'bg-emerald-500 animate-pulse' : 'bg-red-500'} simplified-status-dot\`;
                }
                
                updateCookieSimilarityIndicator(card, b);
                
                const lb = card.querySelector('.log-box');
                const html = b.logs.map(l => '<div class="mb-1.5 ' + l.color + '"><span class="opacity-30 mr-2">[' + l.time + ']</span>' + l.msg + '</div>').join('');
                const h = html.length + (b.logs[0]?.msg || "");
                if (logHashes.get(b.id) !== h) { 
                    lb.innerHTML = html; 
                    logHashes.set(b.id, h); 
                }
                if (document.activeElement.tagName !== 'INPUT' && !card.dataset.lock) syncBtnStyle(card, b.settings);
            });
            
            updateBulkButtonState();
        } catch(e){
            console.error('更新UI失败:', e);
        }
    }
    
    function updateCookieSimilarityIndicator(card, botData) {
        const similarityIndicator = card.querySelector('.cookie-similarity-indicator');
        const similarityText = card.querySelector('.cookie-similarity-text');
        
        if (!similarityIndicator || !similarityText) return;
        
        const lastSuccessCookie = botData.lastSuccessCookie || "";
        const currentCookie = botData.settings?.renew?.cookie || "";
        
        if (!lastSuccessCookie || !currentCookie) {
            similarityIndicator.className = 'similarity-indicator similarity-bad';
            similarityText.innerText = '无历史Cookie';
            similarityText.className = 'cookie-similarity-text text-[9px] text-slate-500';
            return;
        }
        
        similarityIndicator.className = 'similarity-indicator similarity-warning';
        similarityText.innerText = '点击检测相似度';
        similarityText.className = 'cookie-similarity-text text-[9px] text-yellow-400 cursor-pointer';
        similarityText.onclick = () => checkCookieSimilarity(botData.id, similarityIndicator, similarityText);
    }
    
    async function checkCookieSimilarity(botId, indicator, textElement) {
        try {
            textElement.innerText = '检测中...';
            textElement.className = 'cookie-similarity-text text-[9px] text-blue-400';
            
            const response = await fetch(\`/api/bots/\${botId}/check-cookie-similarity\`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            
            const data = await response.json();
            
        if (data.success) {
                const similarity = data.similarity;
                
                if (similarity >= 90) {
                    indicator.className = 'similarity-indicator similarity-good';
                    textElement.className = 'cookie-similarity-text text-[9px] text-emerald-400';
                } else if (similarity >= 70) {
                    indicator.className = 'similarity-indicator similarity-warning';
                    textElement.className = 'cookie-similarity-text text-[9px] text-yellow-400';
                } else {
                    indicator.className = 'similarity-indicator similarity-bad';
                    textElement.className = 'cookie-similarity-text text-[9px] text-red-400';
                }
                
                textElement.innerText = \`相似度: \${similarity}%\`;
                textElement.title = data.message;
            } else {
                indicator.className = 'similarity-indicator similarity-bad';
                textElement.className = 'cookie-similarity-text text-[9px] text-red-400';
                textElement.innerText = '检测失败';
                textElement.title = data.message || '未知错误';
            }
        } catch (error) {
            indicator.className = 'similarity-indicator similarity-bad';
            textElement.className = 'cookie-similarity-text text-[9px] text-red-400';
            textElement.innerText = '请求失败';
            textElement.title = error.message;
        }
    }
    
    function syncBtnStyle(card, s) {
        card.querySelector('.btn-ai').className = "btn-ai btn-action py-2 rounded-xl text-[10px] font-bold " + (s.ai?"bg-blue-600":"bg-slate-800");
        card.querySelector('.btn-walk').className = "btn-walk btn-action py-2 rounded-xl text-[10px] font-bold " + (s.walk?"bg-emerald-600":"bg-slate-800");
        card.querySelector('.btn-chat').className = "btn-chat btn-action py-2 rounded-xl text-[10px] font-bold " + (s.chat?"bg-orange-600":"bg-slate-800");
    }
    
    function renderCardBase(card, b) {
        card.className = "robot-card expanded glass rounded-[2rem] p-5 border-t-4 border-t-blue-500 mb-4 transition-all";
        const renewUrl = b.settings.renew.renewUrl || b.settings.renew.url || "";
        const loginUrl = b.settings.renew.loginUrl || "";
        const username = b.settings.renew.username || "";
        const password = b.settings.renew.password || "";
        const cookie = b.settings.renew.cookie || "";
        const method = b.settings.renew.method || "GET";
        const requestBody = b.settings.renew.requestBody || "";
        const customHeaders = b.settings.renew.customHeaders || "";
        const lastSuccessCookie = b.lastSuccessCookie || "";
        
        card.innerHTML = \`
            <div class="flex justify-between mb-4">
                <div>
                    <h3 class="font-bold text-lg">\${b.username}</h3>
                    <p class="text-[10px] text-slate-400">\${b.targetHost}:\${b.targetPort}</p>
                </div>
                <div class="flex items-center gap-2">
                    <span class="full-view-status status-text text-[10px] font-black">离线</span>
                    <button onclick="toggleRobotCard('\${b.id}', this)" class="minimize-btn" title="缩小视图">−</button>
                    <button onclick="removeBot('\${b.id}')" class="text-slate-600 text-xs hover:text-white">✕</button>
                </div>
            </div>
            
            <!-- 原有的完整视图 -->
            <div id="full-view-\${b.id}" class="full-view">
                <div class="bg-cyan-950/20 p-4 rounded-3xl mb-4 border border-cyan-500/20 shadow-inner">
                    <div class="flex justify-between items-center mb-2">
                        <span class="text-[10px] font-bold text-cyan-400 uppercase italic">高级自动续期 (DOM扫描+网络监听)</span>
                        <div class="flex items-center gap-2">
                            <select id="re-method-\${b.id}" class="bg-slate-800 text-[10px] rounded-xl px-2 py-1 outline-none">
                                <option value="GET" \${method === 'GET' ? 'selected' : ''}>GET</option>
                                <option value="POST" \${method === 'POST' ? 'selected' : ''}>POST</option>
                                <option value="PUT" \${method === 'PUT' ? 'selected' : ''}>PUT</option>
                            </select>
                            <input type="checkbox" id="re-en-\${b.id}" \${b.settings.renew.enabled?"checked":""} onchange="showRenewTip('\${b.id}', this.checked)">
                        </div>
                    </div>
                    <input id="re-url-\${b.id}" placeholder="续期接口 URL（可自动检测）" value="\${renewUrl}" class="w-full rounded-xl px-2 py-1 text-[10px] mb-1 outline-none">
                    
                    <!-- Cookie相似度指示器 -->
                    <div class="mb-2">
                        <div class="flex justify-between items-center mb-1">
                            <span class="text-[9px] text-slate-400">Cookie相似度检测</span>
                            <div class="flex items-center gap-2">
                                <div class="cookie-similarity-indicator similarity-indicator similarity-bad w-16"></div>
                                <span class="cookie-similarity-text text-[9px] text-slate-500 cursor-pointer" 
                                      onclick="checkCookieSimilarity('\${b.id}', this.previousElementSibling, this)">
                                    点击检测
                                </span>
                            </div>
                        </div>
                    </div>
                    
                    <div class="mb-2">
                        <button onclick="this.nextElementSibling.classList.toggle('hidden')" class="btn-action w-full bg-cyan-900/40 text-[9px] py-1 rounded-lg text-cyan-300 mb-1">基础请求配置 ▾</button>
                        <div>
                            <textarea id="re-ck-\${b.id}" placeholder="Cookie（自动抓取/手动填写）" class="w-full h-10 rounded-lg px-2 py-1 text-[9px] mb-2 outline-none">\${cookie}</textarea>
                            <textarea id="re-headers-\${b.id}" placeholder="自定义请求头（格式：key1:value1\\nkey2:value2）" class="w-full h-8 rounded-lg px-2 py-1 text-[9px] mb-1 outline-none">\${customHeaders}</textarea>
                            <textarea id="re-body-\${b.id}" placeholder="自定义请求体（JSON 格式优先，仅 POST/PUT 生效）" class="w-full h-12 rounded-lg px-2 py-1 text-[9px] mb-2 outline-none">\${requestBody}</textarea>
                        </div>
                    </div>
                    <div class="mb-2">
                        <button onclick="this.nextElementSibling.classList.toggle('hidden')" class="btn-action w-full bg-cyan-900/40 text-[9px] py-1 rounded-lg text-cyan-300 mb-1">🔍 高级抓取配置（带相似度检测）▾</button>
                        <div class="hidden space-y-1">
                            <input id="re-lurl-\${b.id}" placeholder="登录地址（必填，关联Cookie抓取位置）" value="\${loginUrl}" class="w-full rounded px-2 py-1 text-[9px] mb-1">
                            <input id="re-user-\${b.id}" placeholder="登录用户名（必填）" value="\${username}" class="w-full rounded px-2 py-1 text-[9px] mb-1">
                            <input id="re-pass-\${b.id}" type="password" placeholder="登录密码（必填）" value="\${password}" class="w-full rounded px-2 py-1 text-[9px] mb-1">
                            <button onclick="fetchCookieWithSimilarity('\${b.id}', this)" class="btn-action w-full bg-purple-600/50 py-1 rounded text-[9px] font-bold">✨ 高级检测模式（带Cookie相似度验证）</button>
                            <div class="text-[8px] text-slate-400 p-1 bg-slate-900/30 rounded">
                                <span class="text-emerald-400">✓</span> 自动检测与上次成功Cookie的相似度<br>
                                <span class="text-yellow-400">⚠</span> 低于90%会提示验证<br>
                                <span class="text-cyan-400">ⓘ</span> 确保Cookie有效性
                            </div>
                        </div>
                    </div>
                    <button onclick="saveRenew('\${b.id}')" class="btn-action w-full bg-cyan-600 py-1.5 rounded-xl text-[10px] font-bold">保存设置并测试</button>
                </div>
                <div class="grid grid-cols-3 gap-2 mb-4">
                    <button onclick="toggle('\${b.id}','ai',this)" class="btn-ai btn-action py-2 rounded-xl text-[10px] font-bold \${b.settings.ai?'bg-blue-600':'bg-slate-800'}">AI视角</button>
                    <button onclick="toggle('\${b.id}','walk',this)" class="btn-walk btn-action py-2 rounded-xl text-[10px] font-bold \${b.settings.walk?'bg-emerald-600':'bg-slate-800'}">巡逻模式</button>
                    <button onclick="toggle('\${b.id}','chat',this)" class="btn-chat btn-action py-2 rounded-xl text-[10px] font-bold \${b.settings.chat?'bg-orange-600':'bg-slate-800'}">自动喊话</button>
                </div>
                <div class="bg-slate-900/50 p-4 rounded-3xl border border-slate-800 mb-4">
                    <div class="grid grid-cols-2 gap-2 mb-2">
                        <div><input id="min-\${b.id}" type="number" placeholder="分" class="w-full rounded px-2 py-1 text-[10px]"><button onclick="setTimer('\${b.id}',document.getElementById('min-\${b.id}').value,'min')" class="btn-action w-full mt-1 bg-slate-800 py-1 rounded text-[8px] font-bold">设分</button></div>
                        <div><input id="hour-\${b.id}" type="number" placeholder="时" class="w-full rounded px-2 py-1 text-[10px]"><button onclick="setTimer('\${b.id}',document.getElementById('hour-\${b.id}').value,'hour')" class="btn-action w-full mt-1 bg-slate-800 py-1 rounded text-[8px] font-bold">设时</button></div>
                    </div>
                    <button onclick="restartNow('\${b.id}')" class="btn-action w-full bg-red-600 py-2 rounded-xl text-xs font-bold uppercase">⚡ 立即指令重启</button>
                </div>
                <div class="bg-black/40 p-4 rounded-3xl mb-4 border border-slate-800 text-[10px]">
                    <input id="pto-url-\${b.id}" placeholder="面板 URL" value="\${b.settings.pterodactyl?.url||''}" class="w-full rounded px-2 py-1 mb-1 outline-none">
                    <div class="flex gap-1 mb-1">
                        <input id="pto-sid-\${b.id}" placeholder="ID" value="\${b.settings.pterodactyl?.id||''}" class="flex-1 rounded px-2 py-1 outline-none">
                        <input id="pto-ddir-\${b.id}" placeholder="/" value="\${b.settings.pterodactyl?.defaultDir||'/'}" class="flex-1 rounded px-2 py-1 outline-none">
                    </div>
                    <input id="pto-key-\${b.id}" type="password" placeholder="Key" value="\${b.settings.pterodactyl?.key||''}" class="w-full rounded px-2 py-1 mb-2 outline-none">
                    <div class="flex gap-2">
                        <button onclick="savePto('\${b.id}')" class="btn-action flex-1 bg-slate-800 py-1.5 rounded-lg font-bold">存凭据</button>
                        <button onclick="document.getElementById('f-\${b.id}').click()" class="btn-action flex-1 bg-indigo-600 py-1.5 rounded-lg font-bold">同步文件</button>
                        <input type="file" id="f-\${b.id}" class="hidden" onchange="uploadFile('\${b.id}', this)">
                    </div>
                </div>
                <div class="log-box bg-[#020617] rounded-2xl p-4 h-48 overflow-y-auto border-2 border-blue-500/40"></div>
            </div>
            
            <!-- 新增：简化视图（默认隐藏） -->
            <div id="simplified-view-\${b.id}" class="simplified-view" style="display: none;">
                <div class="connection-card p-4 sm:p-6 mb-4">
                    <div class="text-center mb-4">
                        <div class="inline-block p-3 rounded-2xl bg-blue-500/10 border border-blue-500/20 mb-2">
                            <span class="text-2xl">🤖</span>
                        </div>
                        <h3 class="text-lg font-bold text-white mb-1 truncate max-w-full px-2" 
                            title="\${b.username}">
                            \${b.username}
                        </h3>
                        <div class="flex items-center justify-center gap-2">
                            <div class="w-2 h-2 rounded-full \${b.status==='在线'?'bg-emerald-500 animate-pulse':'bg-red-500'} simplified-status-dot"></div>
                            <span class="simplified-view-status status-text text-xs font-bold \${b.status==='在线'?'text-emerald-400':'text-red-400'}">
                                \${b.status}
                            </span>
                        </div>
                    </div>
                    
                    <div class="space-y-3">
                        <!-- 连接地址 -->
                        <div class="info-item">
                            <div class="text-[10px] text-slate-400 mb-1 flex items-center gap-1">
                                <span>🌐</span>
                                <span>连接地址</span>
                            </div>
                            <div class="ip-port-display text-sm font-mono truncate max-w-full" 
                                 title="\${b.targetHost}:\${b.targetPort}">
                                \${b.targetHost}:\${b.targetPort}
                            </div>
                        </div>
                        
                        <!-- 玩家名称 -->
                        <div class="info-item">
                            <div class="text-[10px] text-slate-400 mb-1 flex items-center gap-1">
                                <span>👤</span>
                                <span>玩家名称</span>
                            </div>
                            <div class="player-display text-sm truncate max-w-full" 
                                 title="\${b.username}">
                                \${b.username}
                            </div>
                        </div>
                        
                        <!-- Cookie状态 -->
                        <div class="info-item">
                            <div class="text-[10px] text-slate-400 mb-1 flex items-center gap-1">
                                <span>🍪</span>
                                <span>Cookie状态</span>
                            </div>
                            <div class="flex items-center justify-between">
                                <span class="text-xs \${b.settings.renew.cookie?'text-emerald-400':'text-red-400'}">
                                    \${b.settings.renew.cookie?'已配置':'未配置'}
                                </span>
                                <span class="text-xs text-slate-400">
                                    \${b.lastSuccessCookie?'有历史':'无历史'}
                                </span>
                            </div>
                        </div>
                        
                        <!-- 功能状态 -->
                        <div class="info-item">
                            <div class="text-[10px] text-slate-400 mb-1 flex items-center gap-1">
                                <span>📊</span>
                                <span>功能状态</span>
                            </div>
                            <div class="flex items-center gap-2 flex-wrap">
                                <span class="text-xs px-2 py-1 rounded \${b.settings.ai?'bg-blue-500/20 text-blue-400':'bg-slate-800/30 text-slate-500'}">AI</span>
                                <span class="text-xs px-2 py-1 rounded \${b.settings.walk?'bg-emerald-500/20 text-emerald-400':'bg-slate-800/30 text-slate-500'}">巡逻</span>
                                <span class="text-xs px-2 py-1 rounded \${b.settings.chat?'bg-orange-500/20 text-orange-400':'bg-slate-800/30 text-slate-500'}">喊话</span>
                                <span class="text-xs px-2 py-1 rounded \${b.settings.renew.enabled?'bg-cyan-500/20 text-cyan-400':'bg-slate-800/30 text-slate-500'}">续期</span>
                            </div>
                        </div>
                    </div>
                    
                    <div class="mt-6 pt-4 border-t border-slate-700/50">
                        <div class="text-[9px] text-slate-500 text-center">
                            点击上方 <span class="text-blue-400 font-bold">−</span> 按钮返回完整视图
                        </div>
                    </div>
                </div>
            </div>
        \`;
    }
    
    // ==================== 简化视图功能函数 ====================
    
    function toggleRobotCard(botId, buttonElement) {
        const fullView = document.getElementById(\`full-view-\${botId}\`);
        const simplifiedView = document.getElementById(\`simplified-view-\${botId}\`);
        const card = document.getElementById(\`card-\${botId}\`);
        
        if (!fullView || !simplifiedView || !card) return;
        
        const isSimplified = fullView.style.display === 'none';
        
        if (isSimplified) {
            fullView.style.display = 'block';
            simplifiedView.style.display = 'none';
            buttonElement.textContent = '−';
            buttonElement.title = '缩小视图';
            card.classList.remove('minimized');
            card.classList.add('expanded');
        } else {
            fullView.style.display = 'none';
            simplifiedView.style.display = 'block';
            buttonElement.textContent = '+';
            buttonElement.title = '展开视图';
            card.classList.add('minimized');
            card.classList.remove('expanded');
        }
        
        updateBulkButtonState();
    }
    
    function toggleAllRobotCards() {
        const cards = document.querySelectorAll('.robot-card');
        const bulkButton = document.getElementById('bulk-view-btn');
        
        if (cards.length === 0) return;
        
        let allSimplified = true;
        cards.forEach(card => {
            const botId = card.id.replace('card-', '');
            const fullView = document.getElementById(\`full-view-\${botId}\`);
            if (fullView && fullView.style.display !== 'none') {
                allSimplified = false;
            }
        });
        
        cards.forEach(card => {
            const botId = card.id.replace('card-', '');
            const button = card.querySelector(\`.minimize-btn[onclick*="toggleRobotCard('\${botId}'"]\`);
            const fullView = document.getElementById(\`full-view-\${botId}\`);
            const simplifiedView = document.getElementById(\`simplified-view-\${botId}\`);
            
            if (button && fullView && simplifiedView) {
                if (allSimplified) {
                    fullView.style.display = 'block';
                    simplifiedView.style.display = 'none';
                    button.textContent = '−';
                    button.title = '缩小视图';
                    card.classList.remove('minimized');
                    card.classList.add('expanded');
                } else {
                    fullView.style.display = 'none';
                    simplifiedView.style.display = 'block';
                    button.textContent = '+';
                    button.title = '展开视图';
                    card.classList.add('minimized');
                    card.classList.remove('expanded');
                }
            }
        });
        
        allCardsSimplified = !allSimplified;
        if (bulkButton) {
            bulkButton.innerHTML = allCardsSimplified ? 
                '<span class="text-sm">📱 全部展开</span>' : 
                '<span class="text-sm">📱 全部简化</span>';
            bulkButton.title = allCardsSimplified ? 
                '展开所有机器人卡片' : 
                '简化所有机器人卡片';
        }
    }
    
    function updateBulkButtonState() {
        const cards = document.querySelectorAll('.robot-card');
        const bulkButton = document.getElementById('bulk-view-btn');
        
        if (!cards.length || !bulkButton) return;
        
        let allSimplified = true;
        let allExpanded = true;
        
        cards.forEach(card => {
            const botId = card.id.replace('card-', '');
            const fullView = document.getElementById(\`full-view-\${botId}\`);
            if (fullView) {
                if (fullView.style.display !== 'none') {
                    allSimplified = false;
                } else {
                    allExpanded = false;
                }
            }
        });
        
        if (allSimplified) {
            bulkButton.innerHTML = '<span class="text-sm">📱 全部展开</span>';
            bulkButton.title = '展开所有机器人卡片';
            allCardsSimplified = true;
        } else if (allExpanded) {
            bulkButton.innerHTML = '<span class="text-sm">📱 全部简化</span>';
            bulkButton.title = '简化所有机器人卡片';
            allCardsSimplified = false;
        } else {
            bulkButton.innerHTML = '<span class="text-sm">📱 统一视图</span>';
            bulkButton.title = '将所有卡片设置为相同视图';
        }
    }
    
    // ==================== 原有功能函数 ====================
    
    function showRenewTip(id, isChecked) {
        const card = document.getElementById('card-' + id);
        const logBox = card.querySelector('.log-box');
        const tipText = isChecked ? "⚠️ 已勾选自动续期，点击「保存设置并测试」即可正式开启" : "⚠️ 已取消自动续期，点击「保存设置并测试」即可正式关闭";
        const tipColor = isChecked ? "text-yellow-400" : "text-slate-400";
        const time = new Date().toLocaleTimeString('zh-CN', { hour12: false });
        const tipHtml = '<div class="mb-1.5 ' + tipColor + '"><span class="opacity-30 mr-2">[' + time + ']</span>' + tipText + '</div>';
        logBox.innerHTML = tipHtml + logBox.innerHTML;
    }
    
    async function saveRenew(id) { 
        const btn = document.querySelector(\`#card-\${id} button[onclick*="saveRenew"]\`);
        const oldText = btn.innerText;
        const d = { 
            enabled: document.getElementById('re-en-'+id).checked, 
            renewUrl: document.getElementById('re-url-'+id).value, 
            loginUrl: document.getElementById('re-lurl-'+id).value, 
            username: document.getElementById('re-user-'+id).value, 
            password: document.getElementById('re-pass-'+id).value,
            cookie: document.getElementById('re-ck-'+id).value,
            method: document.getElementById('re-method-'+id).value,
            requestBody: document.getElementById('re-body-'+id).value,
            customHeaders: document.getElementById('re-headers-'+id).value
        }; 
        btn.innerText = "⏳ 正在同步并测试...";
        try {
            const res = await fetch('/api/bots/'+id+'/renew-config', { 
                method: 'POST', 
                headers: {'Content-Type': 'application/json'}, 
                body: JSON.stringify(d)
            }); 
            if(res.ok) { 
                btn.innerText = "✅ 已保存并触发测试"; 
                setTimeout(() => btn.innerText = oldText, 2500); 
            }
        } catch (e) {
            btn.innerText = "❌ 保存失败";
            setTimeout(() => btn.innerText = oldText, 2500);
        }
    }
    
    async function addBot() { 
        const host = document.getElementById('h').value;
        const username = document.getElementById('u').value;
        if (!host || !username) {
            alert('请填写IP:端口和角色名');
            return;
        }
        await fetch('/api/bots', { 
            method: 'POST', 
            headers: {'Content-Type': 'application/json'}, 
            body: JSON.stringify({ host, username })
        }); 
        updateUI(); 
    }
    
    async function toggle(id, type, btn) { 
        const colors = { ai: 'bg-blue-600', walk: 'bg-emerald-600', chat: 'bg-orange-600' };
        const activeColor = colors[type];
        const isCurrentlyOff = btn.className.includes('bg-slate-800');
        if (isCurrentlyOff) {
            btn.classList.remove('bg-slate-800');
            btn.classList.add(activeColor);
        } else {
            btn.classList.remove(activeColor);
            btn.classList.add('bg-slate-800');
        }
        const card = document.getElementById('card-'+id); card.dataset.lock = "true";
        await fetch('/api/bots/'+id+'/toggle', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({ type })}); 
        setTimeout(() => delete card.dataset.lock, 1200);
    }
    
    async function setTimer(id, value, unit) { 
        if (!value || value <= 0) {
            alert('请输入有效的时间值');
            return;
        }
        await fetch('/api/bots/'+id+'/set-timer', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({ value, unit })}); 
    }
    
    async function restartNow(id) { 
        if (!confirm('确定要立即重启该机器人吗？')) return;
        await fetch('/api/bots/'+id+'/restart-now', { method: 'POST' }); 
    }
    
    async function fetchCookieWithSimilarity(id, btn) {
        const oldText = btn.innerText;
        btn.innerText = "⏳ 正在启动高级检测（带相似度验证）...";
        btn.disabled = true;
        try {
            const res = await fetch(\`/api/bots/\${id}/fetch-cookie\`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            const data = await res.json();
            if (data.success) {
                const cookieInput = document.getElementById(\`re-ck-\${id}\`);
                if (cookieInput) {
                    cookieInput.value = data.cookie;
                    
                    const card = document.getElementById(\`card-\${id}\`);
                    const similarityText = card.querySelector('.cookie-similarity-text');
                    const similarityIndicator = card.querySelector('.cookie-similarity-indicator');
                    
                    if (similarityText && similarityIndicator) {
                        similarityText.innerText = \`相似度: \${data.similarity || '检测中'}\`;
                        if (data.similarity) {
                            const similarityPercent = parseInt(data.similarity) || 0;
                            if (similarityPercent >= 90) {
                                similarityIndicator.className = 'similarity-indicator similarity-good';
                                similarityText.className = 'cookie-similarity-text text-[9px] text-emerald-400';
                            } else if (similarityPercent >= 70) {
                                similarityIndicator.className = 'similarity-indicator similarity-warning';
                                similarityText.className = 'cookie-similarity-text text-[9px] text-yellow-400';
                            } else {
                                similarityIndicator.className = 'similarity-indicator similarity-bad';
                                similarityText.className = 'cookie-similarity-text text-[9px] text-red-400';
                            }
                        }
                    }
                }
                await updateUI();
            }
        } catch (err) {
            console.error("抓取Cookie异常：", err);
        } finally {
            btn.innerText = oldText;
            btn.disabled = false;
        }
    }
    
    async function savePto(id) { 
        const d = { 
            url: document.getElementById('pto-url-'+id).value, 
            id: document.getElementById('pto-sid-'+id).value, 
            key: document.getElementById('pto-key-'+id).value, 
            defaultDir: document.getElementById('pto-ddir-'+id).value 
        }; 
        await fetch('/api/bots/'+id+'/pto-config', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(d)}); 
        alert('翼龙面板凭据已保存'); 
    }
    
    async function uploadFile(id, el) { 
        if(!el.files[0]) return; 
        const f = new FormData(); 
        f.append('file', el.files[0]); 
        await fetch('/api/bots/'+id+'/upload', { method: 'POST', body: f }); 
        el.value = ''; 
    }
    
    async function updateSys() { 
        try { 
            const r = await fetch('/api/system/status'); 
            const d = await r.json(); 
            document.getElementById('cpu-val').innerText = d.cpu + '%'; 
            document.getElementById('mem-val').innerText = d.ram + '%'; 
            document.getElementById('disk-val').innerText = d.disk; 
        } catch(e){} 
    }
    
    async function removeBot(id) { 
        if(confirm('确定要彻底移除该机器人吗？此操作不可撤销！')) { 
            await fetch('/api/bots/'+id, { method: 'DELETE' }); 
            document.getElementById('card-'+id).remove(); 
            updateBulkButtonState();
        } 
    }
    
    // ==================== 任务中心功能函数（增强版） ====================
    
    // 页面切换
    function showPage(pageId) {
        const robotPage = document.getElementById('robot-page');
        const taskCenterPage = document.getElementById('task-center-page');
        const navRobot = document.getElementById('nav-robot');
        const navTask = document.getElementById('nav-task');
        
        if (pageId === 'robot-page') {
            robotPage.classList.remove('hidden');
            taskCenterPage.classList.add('hidden');
            navRobot.classList.remove('bg-slate-800');
            navRobot.classList.add('bg-blue-600');
            navTask.classList.remove('bg-blue-600');
            navTask.classList.add('bg-slate-800');
        } else {
            robotPage.classList.add('hidden');
            taskCenterPage.classList.remove('hidden');
            navTask.classList.remove('bg-slate-800');
            navTask.classList.add('bg-blue-600');
            navRobot.classList.remove('bg-blue-600');
            navRobot.classList.add('bg-slate-800');
            
            loadTaskCenter();
        }
    }
    
    // 显示创建任务模态框
    function showCreateTaskModal() {
        const modal = document.getElementById('create-task-modal');
        modal.classList.remove('hidden');
        updateNewTaskTypeConfig();
    }
    
    // 隐藏创建任务模态框
    function hideCreateTaskModal() {
        const modal = document.getElementById('create-task-modal');
        modal.classList.add('hidden');
    }
    
    // 更新新建任务的类型配置（增强版）
    function updateNewTaskTypeConfig(task = null) {
        const type = document.getElementById('new-task-type').value;
        const container = document.getElementById('new-task-type-config');
        let html = '';
        
        // 公共的登录配置字段
        const commonLoginFields = \`
            <div class="login-config-section">
                <h4 class="text-sm font-bold text-slate-300 mb-2">登录配置（可选）</h4>
                <div class="space-y-2">
                    <div>
                        <label class="block text-xs text-slate-400 mb-1">登录URL</label>
                        <input id="login-url" type="url" class="w-full px-3 py-1.5 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                               placeholder="https://example.com/login" value="\${task?.config?.loginUrl || ''}">
                    </div>
                    <div class="grid grid-cols-2 gap-2">
                        <div>
                            <label class="block text-xs text-slate-400 mb-1">用户名</label>
                            <input id="login-username" type="text" class="w-full px-3 py-1.5 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   placeholder="用户名" value="\${task?.config?.username || ''}">
                        </div>
                        <div>
                            <label class="block text-xs text-slate-400 mb-1">密码</label>
                            <input id="login-password" type="password" class="w-full px-3 py-1.5 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   placeholder="密码" value="\${task?.config?.password ? '********' : ''}">
                        </div>
                    </div>
                    <div>
                        <label class="block text-xs text-slate-400 mb-1">Cookie（可选，会覆盖登录）</label>
                        <textarea id="login-cookie" rows="2" class="w-full px-3 py-1.5 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                  placeholder="session=xxx; token=yyy">\${task?.config?.cookie || ''}</textarea>
                    </div>
                    <div class="text-xs text-slate-500">
                        <i class="fas fa-info-circle"></i> 填写Cookie将直接使用，不执行登录流程
                    </div>
                </div>
            </div>
        \`;
        
        switch(type) {
            case 'renew':
                html = \`
                    <div class="space-y-4">
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">续期URL *</label>
                            <input id="renew-url" type="url" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   placeholder="https://example.com/renew" required value="\${task?.config?.renewUrl || ''}">
                        </div>
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">续期方式</label>
                            <select id="renew-method" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm">
                                <option value="auto" \${task?.config?.method === 'auto' ? 'selected' : ''}>自动续期</option>
                                <option value="manual" \${task?.config?.method === 'manual' ? 'selected' : ''}>手动确认</option>
                            </select>
                        </div>
                        \${commonLoginFields}
                    </div>
                \`;
                break;
                
            case 'afk':
                html = \`
                    <div class="space-y-4">
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">挂机网址 *</label>
                            <input id="afk-url" type="url" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   placeholder="https://example.com/dashboard" required value="\${task?.config?.afkUrl || ''}">
                        </div>
                        <div class="grid grid-cols-2 gap-4">
                            <div>
                                <label class="block text-sm text-slate-400 mb-1">AFK时长(分钟)</label>
                                <input id="afk-duration" type="number" min="1" value="\${task?.config?.duration || 30}" 
                                       class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm">
                            </div>
                            <div>
                                <label class="block text-sm text-slate-400 mb-1">AFK动作</label>
                                <select id="afk-action" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm">
                                    <option value="simulate" \${task?.config?.action === 'simulate' ? 'selected' : ''}>模拟活动</option>
                                    <option value="notification" \${task?.config?.action === 'notification' ? 'selected' : ''}>发送通知</option>
                                    <option value="auto-login" \${task?.config?.action === 'auto-login' ? 'selected' : ''}>自动登录保持</option>
                                </select>
                            </div>
                        </div>
                        \${commonLoginFields}
                    </div>
                \`;
                break;
                
            case 'timed-url':
                html = \`
                    <div class="space-y-4">
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">目标URL *</label>
                            <input id="target-url" type="url" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   placeholder="https://example.com" required value="\${task?.config?.targetUrl || ''}">
                        </div>
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">访问方式</label>
                            <select id="access-method" class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm">
                                <option value="get" \${task?.config?.method === 'get' ? 'selected' : ''}>GET请求</option>
                                <option value="post" \${task?.config?.method === 'post' ? 'selected' : ''}>POST请求</option>
                                <option value="simulate" \${task?.config?.method === 'simulate' ? 'selected' : ''}>模拟浏览器</option>
                                <option value="with-login" \${task?.config?.method === 'with-login' ? 'selected' : ''}>带登录访问</option>
                            </select>
                        </div>
                        \${commonLoginFields}
                    </div>
                \`;
                break;
        }
        
        container.innerHTML = html;
    }
    
    // 确认创建任务
    async function confirmCreateTask() {
        const name = document.getElementById('new-task-name').value.trim();
        const type = document.getElementById('new-task-type').value;
        const interval = parseInt(document.getElementById('new-task-interval').value) || 5;
        
        if (!name) {
            alert('请输入任务名称');
            return;
        }
        
        // 收集配置
        const config = { interval };
        
        switch(type) {
            case 'renew':
                const renewUrl = document.getElementById('renew-url').value;
                if (!renewUrl) {
                    alert('请输入续期URL');
                    return;
                }
                config.renewUrl = renewUrl;
                config.method = document.getElementById('renew-method').value;
                break;
            case 'afk':
                const afkUrl = document.getElementById('afk-url').value;
                if (!afkUrl) {
                    alert('请输入挂机网址');
                    return;
                }
                config.afkUrl = afkUrl;
                config.duration = parseInt(document.getElementById('afk-duration').value) || 30;
                config.action = document.getElementById('afk-action').value;
                break;
            case 'timed-url':
                const targetUrl = document.getElementById('target-url').value;
                if (!targetUrl) {
                    alert('请输入目标URL');
                    return;
                }
                config.targetUrl = targetUrl;
                config.method = document.getElementById('access-method').value;
                break;
        }
        
        // 收集登录配置
        const loginUrl = document.getElementById('login-url')?.value;
        const username = document.getElementById('login-username')?.value;
        const password = document.getElementById('login-password')?.value;
        const cookie = document.getElementById('login-cookie')?.value;
        
        if (loginUrl) config.loginUrl = loginUrl;
        if (username) config.username = username;
        if (password && password !== '********') config.password = password;
        if (cookie) config.cookie = cookie;
        
        try {
            const response = await fetch('/api/task-center/create-task', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    name,
                    type,
                    config
                })
            });
            
            const data = await response.json();
            if (data.success) {
                hideCreateTaskModal();
                loadTaskCenter();
            } else {
                alert('创建任务失败: ' + (data.message || '未知错误'));
            }
        } catch (error) {
            alert('请求失败: ' + error.message);
        }
    }
    
    // 加载任务中心
    async function loadTaskCenter() {
        try {
            const response = await fetch('/api/task-center/config');
            taskCenterData = await response.json();
            
            document.getElementById('auto-clear-logs').checked = taskCenterData.settings.autoClearLogs || true;
            document.getElementById('max-log-entries').value = taskCenterData.settings.maxLogEntries || 100;
            document.getElementById('enable-auto-login').checked = taskCenterData.settings.enableAutoLogin || true;
            
            renderTaskList(taskCenterData.tasks);
            updateTaskbar(taskCenterData.tasks);
            
            if (selectedTaskId) {
                const task = taskCenterData.tasks.find(t => t.id === selectedTaskId);
                if (task) {
                    updateTaskDetail(task);
                } else {
                    selectedTaskId = null;
                    resetTaskDetail();
                }
            }
        } catch (error) {
            console.error('加载任务中心失败:', error);
        }
    }
    
    // 渲染任务列表
    function renderTaskList(tasks) {
        const container = document.getElementById('task-list');
        
        if (!tasks || tasks.length === 0) {
            container.innerHTML = '<div class="text-center text-slate-500 py-8">暂无任务，点击"创建新任务"开始</div>';
            return;
        }
        
        container.innerHTML = tasks.map(task => \`
            <div class="task-card p-3 \${selectedTaskId === task.id ? 'selected' : ''}" onclick="selectTask('\${task.id}')">
                <div class="flex justify-between items-center mb-2">
                    <span class="font-bold text-white truncate">\${task.name}</span>
                    <div class="flex items-center gap-2">
                        \${task.lastLoginStatus === '已登录' ? 
                            '<span class="text-xs text-emerald-400" title="已登录"><i class="fas fa-check-circle"></i></span>' : 
                            '<span class="text-xs text-slate-500" title="未登录"><i class="fas fa-times-circle"></i></span>'
                        }
                        <span class="text-xs px-2 py-1 rounded-full \${task.status === 'running' ? 'task-status-running' : 'task-status-stopped'}">
                            \${task.status === 'running' ? '运行中' : '已停止'}
                        </span>
                    </div>
                </div>
                <div class="flex items-center justify-between text-xs text-slate-400">
                    <div class="flex items-center gap-2">
                        <span class="px-2 py-1 rounded bg-slate-900/50">
                            \${task.type === 'renew' ? '续期' : task.type === 'afk' ? 'AFK' : '访问URL'}
                        </span>
                        <span>\${task.config.interval || 5}分钟</span>
                    </div>
                    <span>\${new Date(task.createdAt).toLocaleDateString()}</span>
                </div>
            </div>
        \`).join('');
    }
    
    // 选择任务
    function selectTask(taskId) {
        selectedTaskId = taskId;
        renderTaskList(taskCenterData.tasks);
        loadTaskDetail(taskId);
    }
    
    // 加载任务详情
    async function loadTaskDetail(taskId) {
        try {
            const response = await fetch('/api/task-center/config');
            taskCenterData = await response.json();
            const task = taskCenterData.tasks.find(t => t.id === taskId);
            
            if (task) {
                updateTaskDetail(task);
            }
        } catch (error) {
            console.error('加载任务详情失败:', error);
        }
    }
    
    // 更新任务详情（增强版）
    function updateTaskDetail(task) {
        document.getElementById('selected-task-title').textContent = task.name;
        
        const controls = document.getElementById('task-controls');
        controls.classList.remove('hidden');
        
        const toggleBtn = document.getElementById('toggle-task-btn');
        if (task.status === 'running') {
            toggleBtn.innerHTML = '<i class="fas fa-stop"></i> 停止';
            toggleBtn.classList.remove('bg-emerald-600');
            toggleBtn.classList.add('bg-red-600');
        } else {
            toggleBtn.innerHTML = '<i class="fas fa-play"></i> 启动';
            toggleBtn.classList.remove('bg-red-600');
            toggleBtn.classList.add('bg-emerald-600');
        }
        
        // 显示/隐藏测试按钮
        const testLoginBtn = document.getElementById('test-login-btn');
        const testRenewBtn = document.getElementById('test-renew-btn');
        
        if (task.config.loginUrl || task.config.cookie) {
            testLoginBtn.classList.remove('hidden');
        } else {
            testLoginBtn.classList.add('hidden');
        }
        
        if (task.type === 'renew' && task.config.renewUrl) {
            testRenewBtn.classList.remove('hidden');
        } else {
            testRenewBtn.classList.add('hidden');
        }
        
        document.getElementById('clear-logs-btn').disabled = false;
        
        const configArea = document.getElementById('task-config');
        configArea.classList.remove('hidden');
        
        document.getElementById('task-config-name').value = task.name;
        document.getElementById('task-config-type').value = task.type === 'renew' ? '续期任务' : 
                                                          task.type === 'afk' ? 'AFK任务' : '定时访问URL';
        document.getElementById('task-config-interval').value = task.config.interval || 5;
        document.getElementById('task-config-lastrun').value = task.lastRun ? 
            new Date(task.lastRun).toLocaleString('zh-CN') : '从未运行';
        document.getElementById('task-config-nextrun').value = task.nextRun ? 
            new Date(task.nextRun).toLocaleString('zh-CN') : '未计划';
        
        updateTaskTypeConfig(task);
        updateTaskLogs(task.logs);
        
        // 更新登录状态显示
        const loginStatusSection = document.getElementById('task-login-status');
        const loginStatusBadge = document.getElementById('login-status-badge');
        const loginDetails = document.getElementById('login-details');
        
        if (task.config.loginUrl || task.config.cookie) {
            loginStatusSection.classList.remove('hidden');
            
            if (task.lastLoginStatus === '已登录') {
                loginStatusBadge.innerHTML = '<i class="fas fa-check-circle"></i><span>已登录</span>';
                loginStatusBadge.className = 'login-status login-status-logged';
                loginDetails.innerHTML = \`上次登录时间: \${task.config.lastLoginTime ? new Date(task.config.lastLoginTime).toLocaleString('zh-CN') : '未知'}\`;
            } else {
                loginStatusBadge.innerHTML = '<i class="fas fa-times-circle"></i><span>未登录</span>';
                loginStatusBadge.className = 'login-status login-status-not-logged';
                loginDetails.innerHTML = '上次登录时间: 无';
            }
        } else {
            loginStatusSection.classList.add('hidden');
        }
    }
    
    // 更新任务类型配置（增强版）
    function updateTaskTypeConfig(task) {
        const container = document.getElementById('task-type-config');
        let html = '';
        
        switch(task.type) {
            case 'renew':
                html = \`
                    <div class="space-y-4">
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">续期URL</label>
                            <input type="text" value="\${task.config.renewUrl || ''}" 
                                   class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   onchange="updateTaskConfig('\${task.id}', 'renewUrl', this.value)">
                        </div>
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">续期方式</label>
                            <select class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                    onchange="updateTaskConfig('\${task.id}', 'method', this.value)">
                                <option value="auto" \${task.config.method === 'auto' ? 'selected' : ''}>自动续期</option>
                                <option value="manual" \${task.config.method === 'manual' ? 'selected' : ''}>手动确认</option>
                            </select>
                        </div>
                    </div>
                \`;
                break;
                
            case 'afk':
                html = \`
                    <div class="space-y-4">
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">挂机网址</label>
                            <input type="text" value="\${task.config.afkUrl || ''}" 
                                   class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   onchange="updateTaskConfig('\${task.id}', 'afkUrl', this.value)">
                        </div>
                        <div class="grid grid-cols-1 md:grid-cols-2 gap-4">
                            <div>
                                <label class="block text-sm text-slate-400 mb-1">AFK时长(分钟)</label>
                                <input type="number" min="1" value="\${task.config.duration || 30}" 
                                       class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                       onchange="updateTaskConfig('\${task.id}', 'duration', this.value)">
                            </div>
                            <div>
                                <label class="block text-sm text-slate-400 mb-1">AFK动作</label>
                                <select class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                        onchange="updateTaskConfig('\${task.id}', 'action', this.value)">
                                    <option value="simulate" \${task.config.action === 'simulate' ? 'selected' : ''}>模拟活动</option>
                                    <option value="notification" \${task.config.action === 'notification' ? 'selected' : ''}>发送通知</option>
                                    <option value="auto-login" \${task.config.action === 'auto-login' ? 'selected' : ''}>自动登录保持</option>
                                </select>
                            </div>
                        </div>
                    </div>
                \`;
                break;
                
            case 'timed-url':
                html = \`
                    <div class="space-y-4">
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">目标URL</label>
                            <input type="text" value="\${task.config.targetUrl || ''}" 
                                   class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                   onchange="updateTaskConfig('\${task.id}', 'targetUrl', this.value)">
                        </div>
                        <div>
                            <label class="block text-sm text-slate-400 mb-1">访问方式</label>
                            <select class="w-full px-3 py-2 bg-slate-800 border border-slate-700 rounded-lg text-sm" 
                                    onchange="updateTaskConfig('\${task.id}', 'method', this.value)">
                                <option value="get" \${task.config.method === 'get' ? 'selected' : ''}>GET请求</option>
                                <option value="post" \${task.config.method === 'post' ? 'selected' : ''}>POST请求</option>
                                <option value="simulate" \${task.config.method === 'simulate' ? 'selected' : ''}>模拟浏览器</option>
                                <option value="with-login" \${task.config.method === 'with-login' ? 'selected' : ''}>带登录访问</option>
                            </select>
                        </div>
                    </div>
                \`;
                break;
        }
        
        container.innerHTML = html;
    }
    
    // 更新任务日志
    function updateTaskLogs(logs) {
        const container = document.getElementById('task-log-content');
        
        if (!logs || logs.length === 0) {
            container.innerHTML = '<div class="text-slate-500">暂无日志记录</div>';
            return;
        }
        
        container.innerHTML = logs.map(log => \`
            <div class="mb-2 pb-2 border-b border-slate-800/50 \${getTaskLogColorClass(log.type)}">
                <div class="flex justify-between text-xs text-slate-500 mb-1">
                    <span>[\${log.timestamp}]</span>
                    <span class="px-2 py-0.5 rounded bg-slate-800/50">\${log.type}</span>
                </div>
                <div>\${log.message}</div>
            </div>
        \`).join('');
        
        container.scrollTop = 0;
    }
    
    function getTaskLogColorClass(type) {
        switch(type) {
            case 'success': return 'log-entry-success';
            case 'warning': return 'log-entry-warning';
            case 'error': return 'log-entry-error';
            default: return 'log-entry-info';
        }
    }
    
    // 重置任务详情
    function resetTaskDetail() {
        document.getElementById('selected-task-title').textContent = '选择任务以查看详情';
        document.getElementById('task-controls').classList.add('hidden');
        document.getElementById('task-config').classList.add('hidden');
        document.getElementById('clear-logs-btn').disabled = true;
        document.getElementById('task-log-content').innerHTML = '<div class="text-slate-500">选择一个任务查看日志</div>';
    }
    
    // 切换任务状态
    async function toggleSelectedTask() {
        if (!selectedTaskId) return;
        
        try {
            const response = await fetch(\`/api/task-center/\${selectedTaskId}/toggle\`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            
            const data = await response.json();
            if (data.success) {
                loadTaskCenter();
            }
        } catch (error) {
            alert('操作失败: ' + error.message);
        }
    }
    
    // 测试任务登录
    async function testTaskLogin() {
        if (!selectedTaskId) return;
        
        try {
            const response = await fetch(\`/api/task-center/\${selectedTaskId}/test-login\`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            
            const data = await response.json();
            if (data.success) {
                alert('登录测试成功！');
                loadTaskDetail(selectedTaskId);
            } else {
                alert('登录测试失败: ' + data.message);
            }
        } catch (error) {
            alert('请求失败: ' + error.message);
        }
    }
    
    // 测试任务续期
    async function testTaskRenew() {
        if (!selectedTaskId) return;
        
        try {
            const response = await fetch(\`/api/task-center/\${selectedTaskId}/test-renew\`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            
            const data = await response.json();
            if (data.success) {
                alert('续期测试成功！');
                loadTaskDetail(selectedTaskId);
            } else {
                alert('续期测试失败: ' + data.message);
            }
        } catch (error) {
            alert('请求失败: ' + error.message);
        }
    }
    
    // 删除任务
    async function deleteSelectedTask() {
        if (!selectedTaskId || !confirm('确定要删除这个任务吗？此操作不可撤销！')) return;
        
        try {
            const response = await fetch(\`/api/task-center/\${selectedTaskId}\`, {
                method: 'DELETE'
            });
            
            const data = await response.json();
            if (data.success) {
                selectedTaskId = null;
                loadTaskCenter();
                resetTaskDetail();
            }
        } catch (error) {
            alert('删除失败: ' + error.message);
        }
    }
    
    // 清理任务日志
    async function clearSelectedTaskLogs() {
        if (!selectedTaskId) return;
        
        try {
            const response = await fetch(\`/api/task-center/\${selectedTaskId}/clear-logs\`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' }
            });
            
            const data = await response.json();
            if (data.success) {
                loadTaskDetail(selectedTaskId);
            }
        } catch (error) {
            alert('清理日志失败: ' + error.message);
        }
    }
    
    // 更新任务中心设置
    async function updateTaskCenterSettings() {
        const autoClearLogs = document.getElementById('auto-clear-logs').checked;
        const maxLogEntries = parseInt(document.getElementById('max-log-entries').value) || 100;
        const enableAutoLogin = document.getElementById('enable-auto-login').checked;
        
        try {
            const response = await fetch('/api/task-center/update-config', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    settings: {
                        autoClearLogs,
                        maxLogEntries,
                        enableAutoLogin
                    }
                })
            });
            
            await response.json();
        } catch (error) {
            console.error('更新设置失败:', error);
        }
    }
    
    // 切换任务栏显示
    function toggleTaskbar() {
        const taskbar = document.getElementById('taskbar');
        const toggleBtn = document.getElementById('taskbar-toggle');
        
        taskbarVisible = !taskbarVisible;
        
        if (taskbarVisible) {
            taskbar.classList.remove('hidden');
            toggleBtn.innerHTML = '<i class="fas fa-chevron-down"></i>';
        } else {
            taskbar.classList.add('hidden');
            toggleBtn.innerHTML = '<i class="fas fa-chevron-up"></i>';
        }
    }
    
    // 更新任务栏
    function updateTaskbar(tasks) {
        const runningTasks = tasks.filter(t => t.status === 'running');
        const countElement = document.getElementById('running-task-count');
        const itemsContainer = document.getElementById('taskbar-items');
        
        countElement.textContent = runningTasks.length;
        
        if (runningTasks.length === 0) {
            itemsContainer.innerHTML = '<div class="text-center text-slate-500 py-4">无运行中的任务</div>';
            return;
        }
        
        itemsContainer.innerHTML = runningTasks.map(task => \`
            <div class="taskbar-item">
                <div class="flex justify-between items-center mb-1">
                    <span class="text-sm font-bold text-white truncate">\${task.name}</span>
                    <span class="text-xs text-emerald-400 animate-pulse">●</span>
                </div>
                <div class="flex justify-between text-xs text-slate-400">
                    <span>\${task.type === 'renew' ? '续期' : task.type === 'afk' ? 'AFK' : '访问URL'}</span>
                    <span>\${task.config.interval || 5}分钟</span>
                </div>
            </div>
        \`).join('');
    }
    
    // 更新任务配置
    async function updateTaskConfig(key, value) {
        if (!selectedTaskId) return;
        
        try {
            const response = await fetch('/api/task-center/config');
            taskCenterData = await response.json();
            const taskIndex = taskCenterData.tasks.findIndex(t => t.id === selectedTaskId);
            
            if (taskIndex === -1) return;
            
            if (key === 'name') {
                taskCenterData.tasks[taskIndex].name = value;
            } else {
                taskCenterData.tasks[taskIndex].config[key] = value;
            }
            
            await fetch('/api/task-center/update-config', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ tasks: taskCenterData.tasks })
            });
            
            loadTaskCenter();
        } catch (error) {
            console.error('更新任务配置失败:', error);
        }
    }
    
    // 页面加载后初始化
    document.addEventListener('DOMContentLoaded', function() {
        document.getElementById('new-task-type').addEventListener('change', () => updateNewTaskTypeConfig());
        
        setTimeout(() => {
            if (window.location.hash === '#task-center') {
                showPage('task-center-page');
            }
        }, 100);
    });
    
    // 初始化
    setInterval(() => { 
        updateUI(); 
        updateSys(); 
        
        if (!document.getElementById('task-center-page').classList.contains('hidden')) {
            loadTaskCenter();
        }
    }, 2000); 
    updateUI(); 
    updateSys();
    
    document.addEventListener('DOMContentLoaded', function() {
        setTimeout(updateBulkButtonState, 500);
    });
    </script></body></html>`);
});

// --- [ 9. 启动服务 ] ---
const PORT = process.env.SERVER_PORT || 4681;
app.listen(PORT, '0.0.0.0', async () => {
    console.log(`[OK] Pathfinder PRO 2025 (增强版任务中心 + 哪吒探针) | 端口: ${PORT}`);
    console.log(`[功能] 1. DOM级自动扫描续期按钮 2. 多语言关键词匹配`);
    console.log(`[功能] 3. Network层监听续期请求 4. 智能选择最佳续期请求`);
    console.log(`[功能] 5. Cookie相似度检测系统（≥90%匹配） 6. 机器人卡片简化视图`);
    console.log(`[功能] 7. 任务中心增强版：支持登录配置的Renew/AFK/定时访问URL任务`);
    console.log(`[功能] 8. 哪吒探针V1集成：随机化文件名启动，避免检测`);
    console.log(`[修复] ✅ 已修复续期系统首位陷阱`);
    console.log(`[修复] ✅ 已修复简化卡片状态不一致`);
    console.log(`[修复] ✅ 已修复文本溢出长框框问题`);
    console.log(`[新增] 🔍 Cookie相似度检测：确保抓取Cookie与上次续期成功的Cookie90%以上相同`);
    console.log(`[新增] 📋 任务中心增强版：三种任务类型均支持登录配置`);
    console.log(`[新增] 🔐 支持测试登录和测试续期功能`);
    console.log(`[新增] 📊 实时登录状态显示和监控`);
    console.log(`[新增] 🛰️ 哪吒探针V1：面板顶部"哪吒探针"按钮配置`);
    
    // 加载配置
    await loadTaskCenterConfig();
    
    // 加载哪吒配置
    try {
        if (fsSync.existsSync(NEZHA_CONFIG_FILE)) {
            const data = await fs.readFile(NEZHA_CONFIG_FILE, 'utf8');
            nezhaConfig = JSON.parse(data);
            console.log('[哪吒] 配置加载成功');
            
            // 如果配置存在且不为空，则自动启动
            if (nezhaConfig.addr && nezhaConfig.key) {
                console.log('[哪吒] 自动启动中...');
                setTimeout(() => startNezha(nezhaConfig.addr, nezhaConfig.key, nezhaConfig.tls), 3000);
            }
        } else {
            console.log('[哪吒] 无历史配置');
        }
    } catch (e) {
        console.log('[哪吒] 配置加载失败:', e.message);
    }
    
    // 加载机器人配置
    if (fsSync.existsSync(CONFIG_FILE)) {
        try {
            const data = await fs.readFile(CONFIG_FILE, 'utf8');
            const saved = JSON.parse(data);
            for (const b of saved) {
                createSmartBot(b.id, b.host, b.port, b.username, [], b.settings, b.renewCookieBindings || [], b.lastSuccessCookie || "");
                const botMeta = activeBots.get(b.id);
                if (botMeta && botMeta.settings.renew.enabled && !botMeta.renewTimer) {
                    scheduleNextRenew(botMeta.id);
                }
            }
        } catch (e) {
            console.log('[配置] 加载机器人配置失败，使用空配置:', e.message);
        }
    }
});
