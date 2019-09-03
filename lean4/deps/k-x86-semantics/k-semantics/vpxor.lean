def vpxor1 : instruction :=
  definst "vpxor" $ do
    pattern fun (v_2761 : Mem) (v_2762 : reg (bv 128)) (v_2763 : reg (bv 128)) => do
      v_12891 <- getRegister v_2762;
      v_12892 <- evaluateAddress v_2761;
      v_12893 <- load v_12892 16;
      setRegister (lhs.of_reg v_2763) (bv_xor v_12891 v_12893);
      pure ()
    pat_end;
    pattern fun (v_2772 : Mem) (v_2773 : reg (bv 256)) (v_2774 : reg (bv 256)) => do
      v_12896 <- getRegister v_2773;
      v_12897 <- evaluateAddress v_2772;
      v_12898 <- load v_12897 32;
      setRegister (lhs.of_reg v_2774) (bv_xor v_12896 v_12898);
      pure ()
    pat_end
