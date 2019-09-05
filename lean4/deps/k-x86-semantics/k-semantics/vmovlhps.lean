def vmovlhps1 : instruction :=
  definst "vmovlhps" $ do
    pattern fun (v_2893 : reg (bv 128)) (v_2894 : reg (bv 128)) (v_2895 : reg (bv 128)) => do
      v_4843 <- getRegister v_2893;
      v_4845 <- getRegister v_2894;
      setRegister (lhs.of_reg v_2895) (concat (extract v_4843 64 128) (extract v_4845 64 128));
      pure ()
    pat_end
