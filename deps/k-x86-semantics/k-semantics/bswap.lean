def bswap : instruction :=
  definst "bswap" $ do
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister (lhs.of_reg r32_0);
      (v_2 : expression (bv 8)) <- eval (extract v_1 24 32);
      (v_3 : expression (bv 8)) <- eval (extract v_1 16 24);
      (v_4 : expression (bv 8)) <- eval (extract v_1 8 16);
      (v_5 : expression (bv 8)) <- eval (extract v_1 0 8);
      setRegister (lhs.of_reg r32_0) (concat (concat v_2 v_3) (concat v_4 v_5));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister (lhs.of_reg r64_0);
      (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      (v_3 : expression (bv 8)) <- eval (extract v_1 48 56);
      (v_4 : expression (bv 8)) <- eval (extract v_1 40 48);
      (v_5 : expression (bv 8)) <- eval (extract v_1 32 40);
      (v_6 : expression (bv 8)) <- eval (extract v_1 24 32);
      (v_7 : expression (bv 8)) <- eval (extract v_1 16 24);
      (v_8 : expression (bv 8)) <- eval (extract v_1 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_1 0 8);
      setRegister (lhs.of_reg r64_0) (concat (concat (concat v_2 v_3) (concat v_4 v_5)) (concat (concat v_6 v_7) (concat v_8 v_9)));
      pure ()
    pat_end
