def orpd1 : instruction :=
  definst "orpd" $ do
    pattern fun (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_4842 <- getRegister v_3067;
      v_4843 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3067) (bv_or v_4842 v_4843);
      pure ()
    pat_end;
    pattern fun (v_3062 : Mem) (v_3063 : reg (bv 128)) => do
      v_9014 <- getRegister v_3063;
      v_9015 <- evaluateAddress v_3062;
      v_9016 <- load v_9015 16;
      setRegister (lhs.of_reg v_3063) (bv_or v_9014 v_9016);
      pure ()
    pat_end
