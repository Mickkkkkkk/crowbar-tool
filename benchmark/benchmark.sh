#!/bin/bash


if ! [ -d "absexamples/" ]; then
  git clone https://github.com/MarcoScaletta/absexamples/
fi

PROJECT_PATH=../

FILES_TO_LOAD=absexamples/collaboratory
today_date=$(date +'%d%m%Y_%H%M%S')
REPORT_FILE="./reports/results${today_date}.csv"
echo "saving in "  $REPORT_FILE

if [ "$1" == "--clean" ]; then
  $PROJECT_PATH/gradlew clean -p $PROJECT_PATH/
  $PROJECT_PATH/gradlew assemble -p $PROJECT_PATH/
fi

echo "file;class;method;result;error;time" > "./reports/results${today_date}.csv"

SECONDS=0

IFS=$'\n';for file in `find ./$FILES_TO_LOAD -type f -name \*.abs`; do
  if ! [ -f "$file" ]; then
    echo "File $file does not exist"
  else
        echo "Loading $file"
        (java -jar $PROJECT_PATH/build/libs/crowbar.jar -v 0 --full "$file"  --report --report-path $REPORT_FILE) > /dev/null 2>&1
        echo "Done with $file"
  fi
done



