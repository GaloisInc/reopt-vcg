def movups1 : instruction :=
  definst "movups" $ do
    pattern fun (v_2712 : reg (bv 128)) (v_2713 : reg (bv 128)) => do
      v_4129 <- getRegister v_2712;
      setRegister (lhs.of_reg v_2713) v_4129;
      pure ()
    pat_end;
    pattern fun (v_2705 : reg (bv 128)) (v_2704 : Mem) => do
      v_8518 <- evaluateAddress v_2704;
      v_8519 <- getRegister v_2705;
      store v_8518 v_8519 16;
      pure ()
    pat_end;
    pattern fun (v_2708 : Mem) (v_2709 : reg (bv 128)) => do
      v_8759 <- evaluateAddress v_2708;
      v_8760 <- load v_8759 16;
      setRegister (lhs.of_reg v_2709) v_8760;
      pure ()
    pat_end
