def xorpd1 : instruction :=
  definst "xorpd" $ do
    pattern fun (v_3417 : reg (bv 128)) (v_3418 : reg (bv 128)) => do
      v_8027 <- getRegister v_3418;
      v_8028 <- getRegister v_3417;
      setRegister (lhs.of_reg v_3418) (bv_xor v_8027 v_8028);
      pure ()
    pat_end;
    pattern fun (v_3412 : Mem) (v_3413 : reg (bv 128)) => do
      v_13562 <- getRegister v_3413;
      v_13563 <- evaluateAddress v_3412;
      v_13564 <- load v_13563 16;
      setRegister (lhs.of_reg v_3413) (bv_xor v_13562 v_13564);
      pure ()
    pat_end
