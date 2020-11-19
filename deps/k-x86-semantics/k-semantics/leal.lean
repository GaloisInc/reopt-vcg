def leal : instruction :=
  definst "leal" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      setRegister (lhs.of_reg r32_1) v_3;
      pure ()
    pat_end
