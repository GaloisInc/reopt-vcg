def vmovd1 : instruction :=
  definst "vmovd" $ do
    pattern fun (v_2786 : reg (bv 128)) (v_2785 : reg (bv 32)) => do
      v_4747 <- getRegister v_2786;
      setRegister (lhs.of_reg v_2785) (extract v_4747 96 128);
      pure ()
    pat_end;
    pattern fun (v_2794 : reg (bv 32)) (v_2795 : reg (bv 128)) => do
      v_4754 <- getRegister v_2794;
      setRegister (lhs.of_reg v_2795) (concat (expression.bv_nat 96 0) (concat (extract v_4754 0 8) (extract v_4754 8 32)));
      pure ()
    pat_end;
    pattern fun (v_2782 : reg (bv 128)) (v_2781 : Mem) => do
      v_9294 <- evaluateAddress v_2781;
      v_9295 <- getRegister v_2782;
      store v_9294 (extract v_9295 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2790 : Mem) (v_2791 : reg (bv 128)) => do
      v_10140 <- evaluateAddress v_2790;
      v_10141 <- load v_10140 4;
      setRegister (lhs.of_reg v_2791) (concat (expression.bv_nat 96 0) (concat (extract v_10141 0 8) (extract v_10141 8 32)));
      pure ()
    pat_end
