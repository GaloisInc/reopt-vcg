def vmovlhps1 : instruction :=
  definst "vmovlhps" $ do
    pattern fun (v_2842 : reg (bv 128)) (v_2843 : reg (bv 128)) (v_2844 : reg (bv 128)) => do
      v_5158 <- getRegister v_2842;
      v_5160 <- getRegister v_2843;
      setRegister (lhs.of_reg v_2844) (concat (extract v_5158 64 128) (extract v_5160 64 128));
      pure ()
    pat_end
