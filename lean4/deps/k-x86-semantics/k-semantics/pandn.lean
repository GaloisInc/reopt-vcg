def pandn1 : instruction :=
  definst "pandn" $ do
    pattern fun (v_3203 : reg (bv 128)) (v_3204 : reg (bv 128)) => do
      v_6419 <- getRegister v_3204;
      v_6423 <- getRegister v_3203;
      setRegister (lhs.of_reg v_3204) (bv_and (bv_xor v_6419 (mi (bitwidthMInt v_6419) -1)) v_6423);
      pure ()
    pat_end;
    pattern fun (v_3198 : Mem) (v_3199 : reg (bv 128)) => do
      v_10484 <- getRegister v_3199;
      v_10488 <- evaluateAddress v_3198;
      v_10489 <- load v_10488 16;
      setRegister (lhs.of_reg v_3199) (bv_and (bv_xor v_10484 (mi (bitwidthMInt v_10484) -1)) v_10489);
      pure ()
    pat_end
