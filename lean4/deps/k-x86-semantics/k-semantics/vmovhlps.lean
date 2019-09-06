def vmovhlps1 : instruction :=
  definst "vmovhlps" $ do
    pattern fun (v_2894 : reg (bv 128)) (v_2895 : reg (bv 128)) (v_2896 : reg (bv 128)) => do
      v_4846 <- getRegister v_2895;
      v_4848 <- getRegister v_2894;
      setRegister (lhs.of_reg v_2896) (concat (extract v_4846 0 64) (extract v_4848 0 64));
      pure ()
    pat_end
