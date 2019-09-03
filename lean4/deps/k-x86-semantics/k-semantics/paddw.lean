def paddw1 : instruction :=
  definst "paddw" $ do
    pattern fun (v_3174 : reg (bv 128)) (v_3175 : reg (bv 128)) => do
      v_6356 <- getRegister v_3175;
      v_6358 <- getRegister v_3174;
      setRegister (lhs.of_reg v_3175) (concat (add (extract v_6356 0 16) (extract v_6358 0 16)) (concat (add (extract v_6356 16 32) (extract v_6358 16 32)) (concat (add (extract v_6356 32 48) (extract v_6358 32 48)) (concat (add (extract v_6356 48 64) (extract v_6358 48 64)) (concat (add (extract v_6356 64 80) (extract v_6358 64 80)) (concat (add (extract v_6356 80 96) (extract v_6358 80 96)) (concat (add (extract v_6356 96 112) (extract v_6358 96 112)) (add (extract v_6356 112 128) (extract v_6358 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3169 : Mem) (v_3170 : reg (bv 128)) => do
      v_10431 <- getRegister v_3170;
      v_10433 <- evaluateAddress v_3169;
      v_10434 <- load v_10433 16;
      setRegister (lhs.of_reg v_3170) (concat (add (extract v_10431 0 16) (extract v_10434 0 16)) (concat (add (extract v_10431 16 32) (extract v_10434 16 32)) (concat (add (extract v_10431 32 48) (extract v_10434 32 48)) (concat (add (extract v_10431 48 64) (extract v_10434 48 64)) (concat (add (extract v_10431 64 80) (extract v_10434 64 80)) (concat (add (extract v_10431 80 96) (extract v_10434 80 96)) (concat (add (extract v_10431 96 112) (extract v_10434 96 112)) (add (extract v_10431 112 128) (extract v_10434 112 128)))))))));
      pure ()
    pat_end
