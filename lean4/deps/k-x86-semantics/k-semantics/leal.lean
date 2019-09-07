def leal1 : instruction :=
  definst "leal" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      setRegister (lhs.of_reg r32_1) (extract v_2 32 64);
      pure ()
    pat_end
