def psubq1 : instruction :=
  definst "psubq" $ do
    pattern fun (v_3099 : reg (bv 128)) (v_3100 : reg (bv 128)) => do
      v_8373 <- getRegister v_3100;
      v_8375 <- getRegister v_3099;
      setRegister (lhs.of_reg v_3100) (concat (sub (extract v_8373 0 64) (extract v_8375 0 64)) (sub (extract v_8373 64 128) (extract v_8375 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3094 : Mem) (v_3095 : reg (bv 128)) => do
      v_15284 <- getRegister v_3095;
      v_15286 <- evaluateAddress v_3094;
      v_15287 <- load v_15286 16;
      setRegister (lhs.of_reg v_3095) (concat (sub (extract v_15284 0 64) (extract v_15287 0 64)) (sub (extract v_15284 64 128) (extract v_15287 64 128)));
      pure ()
    pat_end
