def bswap1 : instruction :=
  definst "bswap" $ do
    pattern fun (v_3096 : reg (bv 32)) => do
      v_5803 <- getRegister v_3096;
      setRegister (lhs.of_reg v_3096) (concat (concat (extract v_5803 24 32) (extract v_5803 16 24)) (concat (extract v_5803 8 16) (extract v_5803 0 8)));
      pure ()
    pat_end;
    pattern fun (v_3099 : reg (bv 64)) => do
      v_5812 <- getRegister v_3099;
      setRegister (lhs.of_reg v_3099) (concat (concat (concat (extract v_5812 56 64) (extract v_5812 48 56)) (concat (extract v_5812 40 48) (extract v_5812 32 40))) (concat (concat (extract v_5812 24 32) (extract v_5812 16 24)) (concat (extract v_5812 8 16) (extract v_5812 0 8))));
      pure ()
    pat_end
