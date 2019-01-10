const express = require('express')
const shell = require('shelljs');
const cors = require('cors')
const bodyParser = require('body-parser');
const fs = require('fs');
var multer = require('multer'); // v1.0.5
var upload = multer(); // for parsing multipart/form-data


const app = express()
const port = 3000

app.use(bodyParser.json()); // for parsing application/json
app.use(bodyParser.urlencoded({ extended: true })); // for parsing application/x-www-form-urlencoded

app.use(cors())

app.post('/', upload.array(), function (req, res, next) {
    shell.cd('./out/solver/bin')
    setTimeout(function(){
        fs.writeFile("o.smt2", req.body.hey, function(err) {
            if(err) {
                return console.log(err);
            }
            console.log("The file was saved!");
            shell.exec('optimathsat o.smt2', function(code, stdout, stderr) {
                var mySubString = stdout.substring(
                    stdout.lastIndexOf("( ") + 1, 
                    stdout.lastIndexOf(" )")
                );
                mySubString = mySubString.split('(')
                let newStr = [];
                let final = [];
                mySubString.forEach((str) => {
                    if (str.includes('false') || str.includes('true'))
                    newStr.push(str.split(')')[0]);
                })

                newStr.forEach((str) => {
                    final.push({el: str.split(' ')[0], val: str.split(' ')[1]});
                })
                return res.send(final);
            });
        }); 
    }, 2000);  

  });

app.listen(port, () => console.log(`listening on port ${port}!`))