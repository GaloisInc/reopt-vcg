def bswap1 : instruction :=
  definst "bswap" $ do
    pattern fun (v_3005 : reg (bv 32)) => do
      v_6006 <- getRegister v_3005;
      setRegister (lhs.of_reg v_3005) (concat (concat (extract v_6006 24 32) (extract v_6006 16 24)) (concat (extract v_6006 8 16) (extract v_6006 0 8)));
      pure ()
    pat_end;
    pattern fun (v_3009 : reg (bv 64)) => do
      v_6015 <- getRegister v_3009;
      setRegister (lhs.of_reg v_3009) (concat (concat (concat (extract v_6015 56 64) (extract v_6015 48 56)) (concat (extract v_6015 40 48) (extract v_6015 32 40))) (concat (concat (extract v_6015 24 32) (extract v_6015 16 24)) (concat (extract v_6015 8 16) (extract v_6015 0 8))));
      pure ()
    pat_end
