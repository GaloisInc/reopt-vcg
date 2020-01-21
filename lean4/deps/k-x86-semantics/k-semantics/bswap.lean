def bswap : instruction :=
  definst "bswap" $ do
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_0) (concat (concat (extract v_1 24 32) (extract v_1 16 24)) (concat (extract v_1 8 16) (extract v_1 0 8)));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg r64_0) (concat (concat (concat (extract v_1 56 64) (extract v_1 48 56)) (concat (extract v_1 40 48) (extract v_1 32 40))) (concat (concat (extract v_1 24 32) (extract v_1 16 24)) (concat (extract v_1 8 16) (extract v_1 0 8))));
      pure ()
    pat_end
