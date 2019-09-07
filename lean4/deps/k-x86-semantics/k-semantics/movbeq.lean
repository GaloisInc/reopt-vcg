def movbeq1 : instruction :=
  definst "movbeq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg r64_1) (concat (concat (concat (concat (concat (concat (concat (extract v_3 56 64) (extract v_3 48 56)) (extract v_3 40 48)) (extract v_3 32 40)) (extract v_3 24 32)) (extract v_3 16 24)) (extract v_3 8 16)) (extract v_3 0 8));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r64_0;
      store v_2 (concat (concat (concat (concat (concat (concat (concat (extract v_3 56 64) (extract v_3 48 56)) (extract v_3 40 48)) (extract v_3 32 40)) (extract v_3 24 32)) (extract v_3 16 24)) (extract v_3 8 16)) (extract v_3 0 8)) 8;
      pure ()
    pat_end
