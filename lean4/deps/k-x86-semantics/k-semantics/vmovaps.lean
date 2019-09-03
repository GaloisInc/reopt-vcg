def vmovaps1 : instruction :=
  definst "vmovaps" $ do
    pattern fun (v_2712 : Mem) (v_2713 : reg (bv 128)) => do
      v_11073 <- evaluateAddress v_2712;
      v_11074 <- load v_11073 16;
      setRegister (lhs.of_reg v_2713) v_11074;
      pure ()
    pat_end;
    pattern fun (v_2721 : Mem) (v_2722 : reg (bv 256)) => do
      v_11076 <- evaluateAddress v_2721;
      v_11077 <- load v_11076 32;
      setRegister (lhs.of_reg v_2722) v_11077;
      pure ()
    pat_end;
    pattern fun (v_2705 : reg (bv 128)) (v_2704 : Mem) => do
      v_13605 <- evaluateAddress v_2704;
      v_13606 <- getRegister v_2705;
      store v_13605 v_13606 16;
      pure ()
    pat_end;
    pattern fun (v_2709 : reg (bv 256)) (v_2708 : Mem) => do
      v_13608 <- evaluateAddress v_2708;
      v_13609 <- getRegister v_2709;
      store v_13608 v_13609 32;
      pure ()
    pat_end
