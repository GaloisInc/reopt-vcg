def pminuw1 : instruction :=
  definst "pminuw" $ do
    pattern fun (v_2647 : reg (bv 128)) (v_2648 : reg (bv 128)) => do
      v_5354 <- getRegister v_2648;
      v_5355 <- eval (extract v_5354 0 16);
      v_5356 <- getRegister v_2647;
      v_5357 <- eval (extract v_5356 0 16);
      v_5360 <- eval (extract v_5354 16 32);
      v_5361 <- eval (extract v_5356 16 32);
      v_5364 <- eval (extract v_5354 32 48);
      v_5365 <- eval (extract v_5356 32 48);
      v_5368 <- eval (extract v_5354 48 64);
      v_5369 <- eval (extract v_5356 48 64);
      v_5372 <- eval (extract v_5354 64 80);
      v_5373 <- eval (extract v_5356 64 80);
      v_5376 <- eval (extract v_5354 80 96);
      v_5377 <- eval (extract v_5356 80 96);
      v_5380 <- eval (extract v_5354 96 112);
      v_5381 <- eval (extract v_5356 96 112);
      v_5384 <- eval (extract v_5354 112 128);
      v_5385 <- eval (extract v_5356 112 128);
      setRegister (lhs.of_reg v_2648) (concat (mux (ult v_5355 v_5357) v_5355 v_5357) (concat (mux (ult v_5360 v_5361) v_5360 v_5361) (concat (mux (ult v_5364 v_5365) v_5364 v_5365) (concat (mux (ult v_5368 v_5369) v_5368 v_5369) (concat (mux (ult v_5372 v_5373) v_5372 v_5373) (concat (mux (ult v_5376 v_5377) v_5376 v_5377) (concat (mux (ult v_5380 v_5381) v_5380 v_5381) (mux (ult v_5384 v_5385) v_5384 v_5385))))))));
      pure ()
    pat_end;
    pattern fun (v_2642 : Mem) (v_2643 : reg (bv 128)) => do
      v_12724 <- getRegister v_2643;
      v_12725 <- eval (extract v_12724 0 16);
      v_12726 <- evaluateAddress v_2642;
      v_12727 <- load v_12726 16;
      v_12728 <- eval (extract v_12727 0 16);
      v_12731 <- eval (extract v_12724 16 32);
      v_12732 <- eval (extract v_12727 16 32);
      v_12735 <- eval (extract v_12724 32 48);
      v_12736 <- eval (extract v_12727 32 48);
      v_12739 <- eval (extract v_12724 48 64);
      v_12740 <- eval (extract v_12727 48 64);
      v_12743 <- eval (extract v_12724 64 80);
      v_12744 <- eval (extract v_12727 64 80);
      v_12747 <- eval (extract v_12724 80 96);
      v_12748 <- eval (extract v_12727 80 96);
      v_12751 <- eval (extract v_12724 96 112);
      v_12752 <- eval (extract v_12727 96 112);
      v_12755 <- eval (extract v_12724 112 128);
      v_12756 <- eval (extract v_12727 112 128);
      setRegister (lhs.of_reg v_2643) (concat (mux (ult v_12725 v_12728) v_12725 v_12728) (concat (mux (ult v_12731 v_12732) v_12731 v_12732) (concat (mux (ult v_12735 v_12736) v_12735 v_12736) (concat (mux (ult v_12739 v_12740) v_12739 v_12740) (concat (mux (ult v_12743 v_12744) v_12743 v_12744) (concat (mux (ult v_12747 v_12748) v_12747 v_12748) (concat (mux (ult v_12751 v_12752) v_12751 v_12752) (mux (ult v_12755 v_12756) v_12755 v_12756))))))));
      pure ()
    pat_end
