hiphop module Timer(time){ 
  async {
    this.react({[time.signame]: this.sec = 0}); 
    this.intv = setInterval(() =>
      this.react({[time.signame]: ++this.sec}), 1000); 
  }kill{
    clearInterval(this.intv); 
  }
}