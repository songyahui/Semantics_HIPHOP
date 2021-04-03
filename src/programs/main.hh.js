hiphop module Main (
  in name="", 
  in passwd="", 
  in login, 
  in logout, 
  out enableLogin,
  out connState="disconn",
  inout time=0, 
  inout connected) 
{
  fork{
    run Identity(name, passwd, enableLogin);
  }par{ 
    every(login.now) {
      run Authenticate(name,passwd,connState, connected); 
      if(connected.nowval) { 
        run Session(connState,time,logout);
      }else{
        emit connState("error");
      }
    }
  }
}
