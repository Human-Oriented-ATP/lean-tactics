# Web set-up

## Set up a Linux virtual machine

Set up a Linux virtual machine on the cloud using a service like Microsoft Azure, AWS, DigitalOcean or Google Cloud, ensuring during set-up that the virtual machine has SSH and HTTP networking ports open for communication.

The virtual machine should have adequate memory and storage for running multiple instances of the motivated proof interface.

The rest of the instructions assume that the virtual machine is running Ubuntu.

## Install Lean and `elan`

The Lean toolchain installer `elan` can be installed using the following sequence of commands:

```bash
curl -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
chmod +x elan-init.sh
bash elan-init.sh
```

You may need to exit and re-enter the virtual machine for `elan` to be added to `PATH`.

## Clone and set up the web editor

Hosting this repository online required a modified version of the Lean web editor (https://github.com/leanprover-community/lean4web), hosted at https://github.com/Human-Oriented-ATP/motivated-proof-interface. Clone it onto the virtual machine using the command

```bash
git clone https://github.com/Human-Oriented-ATP/motivated-proof-interface.git
```

### Install `lean-tactics`

Go to the `Projects` sub-directory and clone this repository using the command

```bash
git clone https://github.com/Human-Oriented-ATP/lean-tactics.git
```

### Install `npm`

Install the latest version of the node package manager using the commands

```bash
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
source ~/.bashrc
nvm install node npm
```

### Install `bubblewrap`

The web interface uses `bubblewrap` to run the server securely. It can be installed using

```bash
sudo apt-get install bubblewrap
```

### Build the repository

Install all dependencies and build the repository using the commands

```bash
npm install
npm run build
```

## Set up `nginx`

### Install

`nginx` is used to set up a reverse proxy, directing client requests to the local address on which the server is running.

It can be installed using the command
 
```bash
sudo apt install nginx
```

### Configure

It needs to be configured further to set up the reverse proxy and work with web-sockets.

Open the `nginx` configuration file with a text editor:

```bash
sudo nano /etc/nginx/sites-enables/default
```

and replace the `server` configuration the following text

```
server {
    listen 80 default_server;
    listen [::]:80 default_server;

    index index.html index.htm index.nginx-debian.html;

    location / {
        proxy_pass http://localhost:8080;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade; 
        proxy_set_header Connection "Upgrade"; 
    }

    location /websocket/ {
        proxy_pass http://localhost:8080;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "Upgrade";
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
```

### Test

The configuration file can be tested using

```bash
sudo nginx -t
```

### Deploy

Finally, `nginx` can be restarted by typing

```bash
sudo systemctl restart nginx
```

## Run the server

### Install `pm2`

Install `pm2`, a software for managing processes:

```bash
sudo apt install pm2
```

### Run the server

Run the server on port `8080` by running the command

```bash
PORT=8080 pm2 start server/injex.js
```

from the root of the `motivated-proof-interface` directory.

### View the running process

View the running process using

```bash
pm2 status
```

### Save the running process

Save the details of the current running processes using

```bash
pm2 save
```

### Configure `pm2` for start up

To ensure that the server is loaded automatically whenever the virtual machine restarts, run the command immediately after the previous one

```bash
pm2 startup
```

---