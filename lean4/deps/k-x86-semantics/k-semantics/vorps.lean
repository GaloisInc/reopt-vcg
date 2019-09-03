def vorps1 : instruction :=
  definst "vorps" $ do
    pattern fun (v_3152 : Mem) (v_3153 : reg (bv 128)) (v_3154 : reg (bv 128)) => do
      v_10590 <- getRegister v_3153;
      v_10591 <- evaluateAddress v_3152;
      v_10592 <- load v_10591 16;
      setRegister (lhs.of_reg v_3154) (bv_or v_10590 v_10592);
      pure ()
    pat_end;
    pattern fun (v_3163 : Mem) (v_3164 : reg (bv 256)) (v_3165 : reg (bv 256)) => do
      v_10595 <- getRegister v_3164;
      v_10596 <- evaluateAddress v_3163;
      v_10597 <- load v_10596 32;
      setRegister (lhs.of_reg v_3165) (bv_or v_10595 v_10597);
      pure ()
    pat_end
