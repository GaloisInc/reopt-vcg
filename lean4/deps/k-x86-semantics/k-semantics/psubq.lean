def psubq1 : instruction :=
  definst "psubq" $ do
    pattern fun (v_3190 : reg (bv 128)) (v_3191 : reg (bv 128)) => do
      v_8065 <- getRegister v_3191;
      v_8067 <- getRegister v_3190;
      setRegister (lhs.of_reg v_3191) (concat (sub (extract v_8065 0 64) (extract v_8067 0 64)) (sub (extract v_8065 64 128) (extract v_8067 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3187 : reg (bv 128)) => do
      v_14489 <- getRegister v_3187;
      v_14491 <- evaluateAddress v_3186;
      v_14492 <- load v_14491 16;
      setRegister (lhs.of_reg v_3187) (concat (sub (extract v_14489 0 64) (extract v_14492 0 64)) (sub (extract v_14489 64 128) (extract v_14492 64 128)));
      pure ()
    pat_end
