def popcntw1 : instruction :=
  definst "popcntw" $ do
    pattern fun (v_2854 : reg (bv 16)) (v_2855 : reg (bv 16)) => do
      v_6480 <- getRegister v_2854;
      setRegister (lhs.of_reg v_2855) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 0 1)) (concat (expression.bv_nat 1 0) (extract v_6480 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 2 3)) (concat (expression.bv_nat 1 0) (extract v_6480 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 4 5)) (concat (expression.bv_nat 1 0) (extract v_6480 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 6 7)) (concat (expression.bv_nat 1 0) (extract v_6480 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 8 9)) (concat (expression.bv_nat 1 0) (extract v_6480 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 10 11)) (concat (expression.bv_nat 1 0) (extract v_6480 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 12 13)) (concat (expression.bv_nat 1 0) (extract v_6480 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6480 14 15)) (concat (expression.bv_nat 1 0) (extract v_6480 15 16)))))))));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister zf (zeroFlag v_6480);
      setRegister af (expression.bv_nat 1 0);
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2851 : Mem) (v_2850 : reg (bv 16)) => do
      v_13716 <- evaluateAddress v_2851;
      v_13717 <- load v_13716 2;
      setRegister (lhs.of_reg v_2850) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 0 1)) (concat (expression.bv_nat 1 0) (extract v_13717 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 2 3)) (concat (expression.bv_nat 1 0) (extract v_13717 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 4 5)) (concat (expression.bv_nat 1 0) (extract v_13717 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 6 7)) (concat (expression.bv_nat 1 0) (extract v_13717 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 8 9)) (concat (expression.bv_nat 1 0) (extract v_13717 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 10 11)) (concat (expression.bv_nat 1 0) (extract v_13717 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 12 13)) (concat (expression.bv_nat 1 0) (extract v_13717 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13717 14 15)) (concat (expression.bv_nat 1 0) (extract v_13717 15 16)))))))));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister zf (zeroFlag v_13717);
      setRegister af (expression.bv_nat 1 0);
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
