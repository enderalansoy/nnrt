# nnrt

Next next release tool is a goal modeling tool which generates .smt2 files and uses OptimathSAT to solve and reflect results.

Deployed on: http://nnrt.herokuapp.com/app/
(Only use HTTP for now as HTTPS do not work as of now)

Solver backend is deployed on http://206.189.12.143/

## Solver REST API
Accessing the Solver REST API: POST to the above IP url with the parameter 'hey' which should include the whole .smt2 file content.

## Client Installation to your local disk

1. in the base folder, npm install
2. direct your browser to /app/index.html
