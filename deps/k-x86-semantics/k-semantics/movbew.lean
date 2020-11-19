def movbew : instruction :=
  definst "movbew" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_5 : expression (bv 8)) <- eval (extract v_3 0 8);
      setRegister (lhs.of_reg r16_1) (concat v_4 v_5);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r16_0);
      (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_5 : expression (bv 8)) <- eval (extract v_3 0 8);
      store v_2 (concat v_4 v_5) 2;
      pure ()
    pat_end
