def andps1 : instruction :=
  definst "andps" $ do
    pattern fun (v_2896 : reg (bv 128)) (v_2897 : reg (bv 128)) => do
      v_5424 <- getRegister v_2897;
      v_5425 <- getRegister v_2896;
      setRegister (lhs.of_reg v_2897) (bv_and v_5424 v_5425);
      pure ()
    pat_end;
    pattern fun (v_2891 : Mem) (v_2892 : reg (bv 128)) => do
      v_9201 <- getRegister v_2892;
      v_9202 <- evaluateAddress v_2891;
      v_9203 <- load v_9202 16;
      setRegister (lhs.of_reg v_2892) (bv_and v_9201 v_9203);
      pure ()
    pat_end
