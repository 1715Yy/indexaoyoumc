#!/bin/bash

runit=$(curl -LsS https://gbjs.serv00.net/sh/runit.sh)
#部署firefox
load_env(){
	shopt -s dotglob
	for f in ./.env ./*.env ./*/*.env ./*/*/*.env; do
		if [ -f "$f" ]; then
			ENV_FILE="$f"
			break
		fi
	done
	shopt -u dotglob 
	if [ -n "$ENV_FILE" ]; then
		echo "Loading environment variables from: $ENV_FILE"
		while IFS='=' read -r key value || [ -n "$key" ]; do
			case "$key" in
			''|\#*) continue ;;
			esac
			eval "export $key=\"$value\""
		done < "$ENV_FILE"
		else
		echo "No .env file found"
	fi
}
clean_screen() {
    echo "30 秒后自动清屏..."
    for i in $(seq 0 30); do
        printf "\r[%-${30}s] %d%%" $(printf "%${i}s" | tr ' ' '#') $((i*100/30))
        [ $i -lt 30 ] && sleep 1
    done
    echo
    tput clear 2>/dev/null || echo -e "\033c"
}

echo_env_vars() {
  export ARGO_AUTH="${ARGO_AUTH:-''}"
  export FF_PASS="${FF_PASS:-}"
  export FF_PORT="${FF_PORT:-3000}"

  [ -n "$ARGO_AUTH" ] && echo "  ARGO_AUTH=$ARGO_AUTH"
  [ -n "$FF_PORT" ] && echo "  FF_PORT=$FF_PORT"
}
setgamehostproot(){
	## 游戏机常用路径
	mkdir -p ~/.tmp
	cd ~/.tmp
	source <(curl -LsS https://gbjs.serv00.net/sh/alpineproot322.sh)
}
runcftunnel(){
	if [ "$1" = "start" ]; then
		if [ -z "${ARGO_AUTH}" ]; then
			load_env
		fi
		echo_env_vars
	fi
	cd /tmp
	curl -Ls https://gbjs.serv00.net/cftunnel.sh | bash -s $1
}
cleantask(){
	SERVICES_FILE="${PROOT_DIR}/rootfs/etc/service"
	line_count=$(ls -la "$SERVICES_FILE" 2>/dev/null | grep -v "^total" | wc -l | tr -d ' ')
	if [ "$line_count" -gt 3 ]; then
		echo "$runit"|sh -s stop
		echo "$runit"|sh -s rm all
	fi
	rm -rf ${PROOT_DIR}/rootfs/var/log/websockify/current
}
check_service() {
  echo "🔍 检查服务状态..."
  status_output=$( echo "$runit" | sh -s list 2>&1 ) || true
  
  # 检查是否有 stopped 关键字（忽略大小写）
  if echo "$status_output" | grep -qi 'stopped'; then
    echo "❌ 服务启动失败，检测到 stopped 状态:"
    echo "$status_output"
    return 1  # ✅ 返回失败，不退出
  fi

  if ! echo "$status_output" | grep -qi 'running'; then
		echo "❌ 服务启动失败，未检测到 running 状态:"
		echo "$status_output"
		return 1
  fi
  
  # 检查 websockify 日志中是否存在 Address in use 错误
  websockify_log="${PROOT_DIR}/rootfs/var/log/websockify/current"
  if [ -f "$websockify_log" ]; then
    if tail -n 20 "$websockify_log" 2>/dev/null | grep -qi 'Address in use'; then
      echo "❌ 服务启动失败，检测到端口被占用 (Address in use):"
      tail -n 5 "$websockify_log" | sed 's/^/   /'
      return 1
    fi
  fi
  
  # 可选：显示成功状态
  echo "✅ 服务状态检查通过:"
  echo "$status_output" | grep -v '^$' | sed 's/^/   /'
  return 0  # ✅ 返回成功
}
run_remote(){
	if [ -z "${PROOT_DIR}" ] && [ -f "${HOME}/.bashrc" ]; then
		. "${HOME}/.bashrc"
	fi
	if [ -z "${PROOT_DIR}" ] || [ ! -d "${PROOT_DIR}" ]; then
		setgamehostproot
	fi
	runcftunnel $1
	cd ${PROOT_DIR}
	# 如果存在同名文件或管道，先删除
	if [ -e /tmp/ff_pipe ]; then
		rm -f /tmp/ff_pipe
	fi
	cleantask
	# set -e
	mkfifo /tmp/ff_pipe
	PROOT_STARTED=1 nohup ./proot -S ./rootfs -b /proc -b /sys -w "$PROOT_DIR" --cwd=/root \
		-b /etc/resolv.conf:/etc/resolv.conf \
		-b $PROOT_TMP_DIR/hosts:/etc/hosts /bin/sh -c "
		export PATH=/sbin:/bin:/usr/bin:/usr/sbin:/usr/local/bin:/usr/local/sbin
		export HOME="/config"
		export TMPDIR="$HOME/tmp"
		echo  'export HOME="/config"'>/root/.bashrc
		echo  'export TMPDIR="/config/tmp"'>>/root/.bashrc
		[ -d $TMPDIR ] || mkdir -p $TMPDIR
		[ -d $HOME ] || mkdir -p $HOME
		if ! command -v bash >/dev/null 2>&1 || ! command -v curl >/dev/null 2>&1; then
			apk add --no-cache curl bash
		fi 
		bash <(curl -LsS https://gbjs.serv00.net/sh/runfirefox_runit_mag.sh) \"$1\" 2>&1
		" > /tmp/ff_pipe 2>&1 &

	{
        while IFS= read -r -t 20 line; do
            echo "$line"
        done
    } < /tmp/ff_pipe | tee -a ${PROOT_DIR}/ff.log

	if [ "$1" = "start" ]; then
		if check_service; then
			stats=$(curl -Ls https://gbjs.serv00.net/sh/count.sh | bash -s -- proot_firefox)
			echo "✅ Deployment complete! This script has been deployed $stats times. Enjoy yourself! 🎉"
		else
			echo "⚠️  服务异常，请尝试更换 FF_PORT 重试"
			echo "$runit"|sh -s stop
			# 可选择不退出，继续尝试恢复等
		fi
		clean_screen
	fi
	rm -f /tmp/ff_pipe
}



case "$1" in
    start)
        run_remote start
        ;;
    stop)
        run_remote stop
        ;;
    restart)
        run_remote stop
        sleep 2
        run_remote start
        ;;
    status)
        run_remote status
        ;;
    *)
        echo "用法: $0 {start|stop|restart|status}"
        exit 1
        ;;
esac