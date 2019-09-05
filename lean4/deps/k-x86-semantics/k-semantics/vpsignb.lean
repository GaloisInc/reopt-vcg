def vpsignb1 : instruction :=
  definst "vpsignb" $ do
    pattern fun (v_3071 : reg (bv 128)) (v_3072 : reg (bv 128)) (v_3073 : reg (bv 128)) => do
      v_7381 <- getRegister v_3071;
      v_7382 <- eval (extract v_7381 0 8);
      v_7384 <- getRegister v_3072;
      v_7385 <- eval (extract v_7384 0 8);
      v_7391 <- eval (extract v_7381 8 16);
      v_7393 <- eval (extract v_7384 8 16);
      v_7399 <- eval (extract v_7381 16 24);
      v_7401 <- eval (extract v_7384 16 24);
      v_7407 <- eval (extract v_7381 24 32);
      v_7409 <- eval (extract v_7384 24 32);
      v_7415 <- eval (extract v_7381 32 40);
      v_7417 <- eval (extract v_7384 32 40);
      v_7423 <- eval (extract v_7381 40 48);
      v_7425 <- eval (extract v_7384 40 48);
      v_7431 <- eval (extract v_7381 48 56);
      v_7433 <- eval (extract v_7384 48 56);
      v_7439 <- eval (extract v_7381 56 64);
      v_7441 <- eval (extract v_7384 56 64);
      v_7447 <- eval (extract v_7381 64 72);
      v_7449 <- eval (extract v_7384 64 72);
      v_7455 <- eval (extract v_7381 72 80);
      v_7457 <- eval (extract v_7384 72 80);
      v_7463 <- eval (extract v_7381 80 88);
      v_7465 <- eval (extract v_7384 80 88);
      v_7471 <- eval (extract v_7381 88 96);
      v_7473 <- eval (extract v_7384 88 96);
      v_7479 <- eval (extract v_7381 96 104);
      v_7481 <- eval (extract v_7384 96 104);
      v_7487 <- eval (extract v_7381 104 112);
      v_7489 <- eval (extract v_7384 104 112);
      v_7495 <- eval (extract v_7381 112 120);
      v_7497 <- eval (extract v_7384 112 120);
      v_7503 <- eval (extract v_7381 120 128);
      v_7505 <- eval (extract v_7384 120 128);
      setRegister (lhs.of_reg v_3073) (concat (mux (sgt v_7382 (expression.bv_nat 8 0)) v_7385 (mux (eq v_7382 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7385 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7391 (expression.bv_nat 8 0)) v_7393 (mux (eq v_7391 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7393 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7399 (expression.bv_nat 8 0)) v_7401 (mux (eq v_7399 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7401 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7407 (expression.bv_nat 8 0)) v_7409 (mux (eq v_7407 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7409 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7415 (expression.bv_nat 8 0)) v_7417 (mux (eq v_7415 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7417 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7423 (expression.bv_nat 8 0)) v_7425 (mux (eq v_7423 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7425 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7431 (expression.bv_nat 8 0)) v_7433 (mux (eq v_7431 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7433 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7439 (expression.bv_nat 8 0)) v_7441 (mux (eq v_7439 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7441 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7447 (expression.bv_nat 8 0)) v_7449 (mux (eq v_7447 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7449 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7455 (expression.bv_nat 8 0)) v_7457 (mux (eq v_7455 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7457 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7463 (expression.bv_nat 8 0)) v_7465 (mux (eq v_7463 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7465 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7471 (expression.bv_nat 8 0)) v_7473 (mux (eq v_7471 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7473 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7479 (expression.bv_nat 8 0)) v_7481 (mux (eq v_7479 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7481 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7487 (expression.bv_nat 8 0)) v_7489 (mux (eq v_7487 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7489 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7495 (expression.bv_nat 8 0)) v_7497 (mux (eq v_7495 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7497 (expression.bv_nat 8 255))))) (mux (sgt v_7503 (expression.bv_nat 8 0)) v_7505 (mux (eq v_7503 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7505 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3065 : Mem) (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_13667 <- evaluateAddress v_3065;
      v_13668 <- load v_13667 16;
      v_13669 <- eval (extract v_13668 0 8);
      v_13671 <- getRegister v_3066;
      v_13672 <- eval (extract v_13671 0 8);
      v_13678 <- eval (extract v_13668 8 16);
      v_13680 <- eval (extract v_13671 8 16);
      v_13686 <- eval (extract v_13668 16 24);
      v_13688 <- eval (extract v_13671 16 24);
      v_13694 <- eval (extract v_13668 24 32);
      v_13696 <- eval (extract v_13671 24 32);
      v_13702 <- eval (extract v_13668 32 40);
      v_13704 <- eval (extract v_13671 32 40);
      v_13710 <- eval (extract v_13668 40 48);
      v_13712 <- eval (extract v_13671 40 48);
      v_13718 <- eval (extract v_13668 48 56);
      v_13720 <- eval (extract v_13671 48 56);
      v_13726 <- eval (extract v_13668 56 64);
      v_13728 <- eval (extract v_13671 56 64);
      v_13734 <- eval (extract v_13668 64 72);
      v_13736 <- eval (extract v_13671 64 72);
      v_13742 <- eval (extract v_13668 72 80);
      v_13744 <- eval (extract v_13671 72 80);
      v_13750 <- eval (extract v_13668 80 88);
      v_13752 <- eval (extract v_13671 80 88);
      v_13758 <- eval (extract v_13668 88 96);
      v_13760 <- eval (extract v_13671 88 96);
      v_13766 <- eval (extract v_13668 96 104);
      v_13768 <- eval (extract v_13671 96 104);
      v_13774 <- eval (extract v_13668 104 112);
      v_13776 <- eval (extract v_13671 104 112);
      v_13782 <- eval (extract v_13668 112 120);
      v_13784 <- eval (extract v_13671 112 120);
      v_13790 <- eval (extract v_13668 120 128);
      v_13792 <- eval (extract v_13671 120 128);
      setRegister (lhs.of_reg v_3067) (concat (mux (sgt v_13669 (expression.bv_nat 8 0)) v_13672 (mux (eq v_13669 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13672 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13678 (expression.bv_nat 8 0)) v_13680 (mux (eq v_13678 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13680 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13686 (expression.bv_nat 8 0)) v_13688 (mux (eq v_13686 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13688 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13694 (expression.bv_nat 8 0)) v_13696 (mux (eq v_13694 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13696 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13702 (expression.bv_nat 8 0)) v_13704 (mux (eq v_13702 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13704 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13710 (expression.bv_nat 8 0)) v_13712 (mux (eq v_13710 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13712 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13718 (expression.bv_nat 8 0)) v_13720 (mux (eq v_13718 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13720 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13726 (expression.bv_nat 8 0)) v_13728 (mux (eq v_13726 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13728 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13734 (expression.bv_nat 8 0)) v_13736 (mux (eq v_13734 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13736 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13742 (expression.bv_nat 8 0)) v_13744 (mux (eq v_13742 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13744 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13750 (expression.bv_nat 8 0)) v_13752 (mux (eq v_13750 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13752 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13758 (expression.bv_nat 8 0)) v_13760 (mux (eq v_13758 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13760 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13766 (expression.bv_nat 8 0)) v_13768 (mux (eq v_13766 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13768 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13774 (expression.bv_nat 8 0)) v_13776 (mux (eq v_13774 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13776 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13782 (expression.bv_nat 8 0)) v_13784 (mux (eq v_13782 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13784 (expression.bv_nat 8 255))))) (mux (sgt v_13790 (expression.bv_nat 8 0)) v_13792 (mux (eq v_13790 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13792 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
