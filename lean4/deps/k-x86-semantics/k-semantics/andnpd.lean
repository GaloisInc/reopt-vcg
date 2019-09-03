def andnpd1 : instruction :=
  definst "andnpd" $ do
    pattern fun (v_2794 : reg (bv 128)) (v_2795 : reg (bv 128)) => do
      v_5404 <- getRegister v_2795;
      v_5408 <- getRegister v_2794;
      setRegister (lhs.of_reg v_2795) (bv_and (bv_xor v_5404 (mi (bitwidthMInt v_5404) -1)) v_5408);
      pure ()
    pat_end;
    pattern fun (v_2789 : Mem) (v_2790 : reg (bv 128)) => do
      v_9360 <- getRegister v_2790;
      v_9364 <- evaluateAddress v_2789;
      v_9365 <- load v_9364 16;
      setRegister (lhs.of_reg v_2790) (bv_and (bv_xor v_9360 (mi (bitwidthMInt v_9360) -1)) v_9365);
      pure ()
    pat_end
