def vmovlhps1 : instruction :=
  definst "vmovlhps" $ do
    pattern fun (v_2918 : reg (bv 128)) (v_2919 : reg (bv 128)) (v_2920 : reg (bv 128)) => do
      v_4870 <- getRegister v_2918;
      v_4872 <- getRegister v_2919;
      setRegister (lhs.of_reg v_2920) (concat (extract v_4870 64 128) (extract v_4872 64 128));
      pure ()
    pat_end
