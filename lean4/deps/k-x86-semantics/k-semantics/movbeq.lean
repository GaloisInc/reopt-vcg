def movbeq : instruction :=
  definst "movbeq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_5 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_6 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_7 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_8 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_11 : expression (bv 8)) <- eval (extract v_3 0 8);
      setRegister (lhs.of_reg r64_1) (concat (concat (concat (concat (concat (concat (concat v_4 v_5) v_6) v_7) v_8) v_9) v_10) v_11);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r64_0);
      (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_5 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_6 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_7 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_8 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_11 : expression (bv 8)) <- eval (extract v_3 0 8);
      store v_2 (concat (concat (concat (concat (concat (concat (concat v_4 v_5) v_6) v_7) v_8) v_9) v_10) v_11) 8;
      pure ()
    pat_end
