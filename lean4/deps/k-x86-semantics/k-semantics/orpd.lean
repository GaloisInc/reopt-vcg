def orpd1 : instruction :=
  definst "orpd" $ do
    pattern fun (v_3041 : reg (bv 128)) (v_3042 : reg (bv 128)) => do
      v_4815 <- getRegister v_3042;
      v_4816 <- getRegister v_3041;
      setRegister (lhs.of_reg v_3042) (bv_or v_4815 v_4816);
      pure ()
    pat_end;
    pattern fun (v_3036 : Mem) (v_3037 : reg (bv 128)) => do
      v_8987 <- getRegister v_3037;
      v_8988 <- evaluateAddress v_3036;
      v_8989 <- load v_8988 16;
      setRegister (lhs.of_reg v_3037) (bv_or v_8987 v_8989);
      pure ()
    pat_end
