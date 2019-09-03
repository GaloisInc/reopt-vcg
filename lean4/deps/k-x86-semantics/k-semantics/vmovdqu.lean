def vmovdqu1 : instruction :=
  definst "vmovdqu" $ do
    pattern fun (v_2787 : Mem) (v_2788 : reg (bv 128)) => do
      v_10301 <- evaluateAddress v_2787;
      v_10302 <- load v_10301 16;
      setRegister (lhs.of_reg v_2788) v_10302;
      pure ()
    pat_end;
    pattern fun (v_2796 : Mem) (v_2797 : reg (bv 256)) => do
      v_10304 <- evaluateAddress v_2796;
      v_10305 <- load v_10304 32;
      setRegister (lhs.of_reg v_2797) v_10305;
      pure ()
    pat_end;
    pattern fun (v_2780 : reg (bv 128)) (v_2779 : Mem) => do
      v_12734 <- evaluateAddress v_2779;
      v_12735 <- getRegister v_2780;
      store v_12734 v_12735 16;
      pure ()
    pat_end;
    pattern fun (v_2784 : reg (bv 256)) (v_2783 : Mem) => do
      v_12737 <- evaluateAddress v_2783;
      v_12738 <- getRegister v_2784;
      store v_12737 v_12738 32;
      pure ()
    pat_end
