def vpandn1 : instruction :=
  definst "vpandn" $ do
    pattern fun (v_2538 : Mem) (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) => do
      v_15205 <- getRegister v_2539;
      v_15209 <- evaluateAddress v_2538;
      v_15210 <- load v_15209 16;
      setRegister (lhs.of_reg v_2540) (bv_and (bv_xor v_15205 (mi (bitwidthMInt v_15205) -1)) v_15210);
      pure ()
    pat_end;
    pattern fun (v_2549 : Mem) (v_2550 : reg (bv 256)) (v_2551 : reg (bv 256)) => do
      v_15213 <- getRegister v_2550;
      v_15217 <- evaluateAddress v_2549;
      v_15218 <- load v_15217 32;
      setRegister (lhs.of_reg v_2551) (bv_and (bv_xor v_15213 (mi (bitwidthMInt v_15213) -1)) v_15218);
      pure ()
    pat_end
