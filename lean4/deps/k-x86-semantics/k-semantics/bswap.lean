def bswap1 : instruction :=
  definst "bswap" $ do
    pattern fun (v_3018 : reg (bv 32)) => do
      v_6161 <- getRegister v_3018;
      setRegister (lhs.of_reg v_3018) (concat (concat (extract v_6161 24 32) (extract v_6161 16 24)) (concat (extract v_6161 8 16) (extract v_6161 0 8)));
      pure ()
    pat_end;
    pattern fun (v_3022 : reg (bv 64)) => do
      v_6170 <- getRegister v_3022;
      setRegister (lhs.of_reg v_3022) (concat (concat (concat (extract v_6170 56 64) (extract v_6170 48 56)) (concat (extract v_6170 40 48) (extract v_6170 32 40))) (concat (concat (extract v_6170 24 32) (extract v_6170 16 24)) (concat (extract v_6170 8 16) (extract v_6170 0 8))));
      pure ()
    pat_end
