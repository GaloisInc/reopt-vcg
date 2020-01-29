def leaw : instruction :=
  definst "leaw" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      (v_3 : expression (bv 16)) <- eval (extract v_2 48 64);
      setRegister (lhs.of_reg r16_1) v_3;
      pure ()
    pat_end
