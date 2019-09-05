def bswap1 : instruction :=
  definst "bswap" $ do
    pattern fun (v_3068 : reg (bv 32)) => do
      v_5922 <- getRegister v_3068;
      setRegister (lhs.of_reg v_3068) (concat (concat (extract v_5922 24 32) (extract v_5922 16 24)) (concat (extract v_5922 8 16) (extract v_5922 0 8)));
      pure ()
    pat_end;
    pattern fun (v_3073 : reg (bv 64)) => do
      v_5931 <- getRegister v_3073;
      setRegister (lhs.of_reg v_3073) (concat (concat (concat (extract v_5931 56 64) (extract v_5931 48 56)) (concat (extract v_5931 40 48) (extract v_5931 32 40))) (concat (concat (extract v_5931 24 32) (extract v_5931 16 24)) (concat (extract v_5931 8 16) (extract v_5931 0 8))));
      pure ()
    pat_end
