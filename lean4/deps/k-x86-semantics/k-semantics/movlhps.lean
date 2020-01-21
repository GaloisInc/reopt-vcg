def movlhps : instruction :=
  definst "movlhps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 64 128) (extract v_3 64 128));
      pure ()
    pat_end
