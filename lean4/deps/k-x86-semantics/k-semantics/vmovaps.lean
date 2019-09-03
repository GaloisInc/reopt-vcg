def vmovaps1 : instruction :=
  definst "vmovaps" $ do
    pattern fun (v_2699 : Mem) (v_2700 : reg (bv 128)) => do
      v_10268 <- evaluateAddress v_2699;
      v_10269 <- load v_10268 16;
      setRegister (lhs.of_reg v_2700) v_10269;
      pure ()
    pat_end;
    pattern fun (v_2708 : Mem) (v_2709 : reg (bv 256)) => do
      v_10271 <- evaluateAddress v_2708;
      v_10272 <- load v_10271 32;
      setRegister (lhs.of_reg v_2709) v_10272;
      pure ()
    pat_end;
    pattern fun (v_2692 : reg (bv 128)) (v_2691 : Mem) => do
      v_12728 <- evaluateAddress v_2691;
      v_12729 <- getRegister v_2692;
      store v_12728 v_12729 16;
      pure ()
    pat_end;
    pattern fun (v_2696 : reg (bv 256)) (v_2695 : Mem) => do
      v_12731 <- evaluateAddress v_2695;
      v_12732 <- getRegister v_2696;
      store v_12731 v_12732 32;
      pure ()
    pat_end
