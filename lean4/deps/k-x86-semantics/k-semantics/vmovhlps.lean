def vmovhlps1 : instruction :=
  definst "vmovhlps" $ do
    pattern fun (v_2869 : reg (bv 128)) (v_2870 : reg (bv 128)) (v_2871 : reg (bv 128)) => do
      v_4819 <- getRegister v_2870;
      v_4821 <- getRegister v_2869;
      setRegister (lhs.of_reg v_2871) (concat (extract v_4819 0 64) (extract v_4821 0 64));
      pure ()
    pat_end
