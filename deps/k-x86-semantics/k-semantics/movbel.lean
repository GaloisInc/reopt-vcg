def movbel : instruction :=
  definst "movbel" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      (v_4 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_5 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_6 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_3 0 8);
      setRegister (lhs.of_reg r32_1) (concat (concat (concat v_4 v_5) v_6) v_7);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r32_0);
      (v_4 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_5 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_6 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_3 0 8);
      store v_2 (concat (concat (concat v_4 v_5) v_6) v_7) 4;
      pure ()
    pat_end
