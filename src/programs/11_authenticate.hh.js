hiphop module Authenticate(
  in name,
  in passwd,
  out connState, 
  out connected) 
{ 
  emit connState("connecting");
  async connected {
    authenticateSvc(name.nowval, passwd.nowval).post().then(v => this.notify(v));
  }
}