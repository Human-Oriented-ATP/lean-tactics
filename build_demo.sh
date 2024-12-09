rm -rf _site/*
lake exe demo
cd _site
firefox localhost:8800 &
python3 -m http.server 8800