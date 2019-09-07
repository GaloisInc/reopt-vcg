def movlhps1 : instruction :=
  definst "movlhps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 64 128) (extract v_3 64 128));
      pure ()
    pat_end
