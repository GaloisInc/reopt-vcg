def paddw1 : instruction :=
  definst "paddw" $ do
    pattern fun (v_3186 : reg (bv 128)) (v_3187 : reg (bv 128)) => do
      v_6339 <- getRegister v_3187;
      v_6341 <- getRegister v_3186;
      setRegister (lhs.of_reg v_3187) (concat (add (extract v_6339 0 16) (extract v_6341 0 16)) (concat (add (extract v_6339 16 32) (extract v_6341 16 32)) (concat (add (extract v_6339 32 48) (extract v_6341 32 48)) (concat (add (extract v_6339 48 64) (extract v_6341 48 64)) (concat (add (extract v_6339 64 80) (extract v_6341 64 80)) (concat (add (extract v_6339 80 96) (extract v_6341 80 96)) (concat (add (extract v_6339 96 112) (extract v_6341 96 112)) (add (extract v_6339 112 128) (extract v_6341 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3182 : Mem) (v_3183 : reg (bv 128)) => do
      v_10402 <- getRegister v_3183;
      v_10404 <- evaluateAddress v_3182;
      v_10405 <- load v_10404 16;
      setRegister (lhs.of_reg v_3183) (concat (add (extract v_10402 0 16) (extract v_10405 0 16)) (concat (add (extract v_10402 16 32) (extract v_10405 16 32)) (concat (add (extract v_10402 32 48) (extract v_10405 32 48)) (concat (add (extract v_10402 48 64) (extract v_10405 48 64)) (concat (add (extract v_10402 64 80) (extract v_10405 64 80)) (concat (add (extract v_10402 80 96) (extract v_10405 80 96)) (concat (add (extract v_10402 96 112) (extract v_10405 96 112)) (add (extract v_10402 112 128) (extract v_10405 112 128)))))))));
      pure ()
    pat_end
