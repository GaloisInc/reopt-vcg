def vpor1 : instruction :=
  definst "vpor" $ do
    pattern fun (v_2968 : Mem) (v_2969 : reg (bv 128)) (v_2970 : reg (bv 128)) => do
      v_13466 <- getRegister v_2969;
      v_13467 <- evaluateAddress v_2968;
      v_13468 <- load v_13467 16;
      setRegister (lhs.of_reg v_2970) (bv_or v_13466 v_13468);
      pure ()
    pat_end;
    pattern fun (v_2979 : Mem) (v_2981 : reg (bv 256)) (v_2982 : reg (bv 256)) => do
      v_13471 <- getRegister v_2981;
      v_13472 <- evaluateAddress v_2979;
      v_13473 <- load v_13472 32;
      setRegister (lhs.of_reg v_2982) (bv_or v_13471 v_13473);
      pure ()
    pat_end
