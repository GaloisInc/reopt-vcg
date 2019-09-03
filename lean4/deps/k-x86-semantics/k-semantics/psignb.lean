def psignb1 : instruction :=
  definst "psignb" $ do
    pattern fun (v_2932 : reg (bv 128)) (v_2933 : reg (bv 128)) => do
      v_7423 <- getRegister v_2932;
      v_7424 <- eval (extract v_7423 0 8);
      v_7426 <- getRegister v_2933;
      v_7427 <- eval (extract v_7426 0 8);
      v_7435 <- eval (extract v_7423 8 16);
      v_7437 <- eval (extract v_7426 8 16);
      v_7445 <- eval (extract v_7423 16 24);
      v_7447 <- eval (extract v_7426 16 24);
      v_7455 <- eval (extract v_7423 24 32);
      v_7457 <- eval (extract v_7426 24 32);
      v_7465 <- eval (extract v_7423 32 40);
      v_7467 <- eval (extract v_7426 32 40);
      v_7475 <- eval (extract v_7423 40 48);
      v_7477 <- eval (extract v_7426 40 48);
      v_7485 <- eval (extract v_7423 48 56);
      v_7487 <- eval (extract v_7426 48 56);
      v_7495 <- eval (extract v_7423 56 64);
      v_7497 <- eval (extract v_7426 56 64);
      v_7505 <- eval (extract v_7423 64 72);
      v_7507 <- eval (extract v_7426 64 72);
      v_7515 <- eval (extract v_7423 72 80);
      v_7517 <- eval (extract v_7426 72 80);
      v_7525 <- eval (extract v_7423 80 88);
      v_7527 <- eval (extract v_7426 80 88);
      v_7535 <- eval (extract v_7423 88 96);
      v_7537 <- eval (extract v_7426 88 96);
      v_7545 <- eval (extract v_7423 96 104);
      v_7547 <- eval (extract v_7426 96 104);
      v_7555 <- eval (extract v_7423 104 112);
      v_7557 <- eval (extract v_7426 104 112);
      v_7565 <- eval (extract v_7423 112 120);
      v_7567 <- eval (extract v_7426 112 120);
      v_7575 <- eval (extract v_7423 120 128);
      v_7577 <- eval (extract v_7426 120 128);
      setRegister (lhs.of_reg v_2933) (concat (mux (sgt v_7424 (expression.bv_nat 8 0)) v_7427 (mux (eq v_7424 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7427 (mi (bitwidthMInt v_7427) -1))))) (concat (mux (sgt v_7435 (expression.bv_nat 8 0)) v_7437 (mux (eq v_7435 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7437 (mi (bitwidthMInt v_7437) -1))))) (concat (mux (sgt v_7445 (expression.bv_nat 8 0)) v_7447 (mux (eq v_7445 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7447 (mi (bitwidthMInt v_7447) -1))))) (concat (mux (sgt v_7455 (expression.bv_nat 8 0)) v_7457 (mux (eq v_7455 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7457 (mi (bitwidthMInt v_7457) -1))))) (concat (mux (sgt v_7465 (expression.bv_nat 8 0)) v_7467 (mux (eq v_7465 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7467 (mi (bitwidthMInt v_7467) -1))))) (concat (mux (sgt v_7475 (expression.bv_nat 8 0)) v_7477 (mux (eq v_7475 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7477 (mi (bitwidthMInt v_7477) -1))))) (concat (mux (sgt v_7485 (expression.bv_nat 8 0)) v_7487 (mux (eq v_7485 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7487 (mi (bitwidthMInt v_7487) -1))))) (concat (mux (sgt v_7495 (expression.bv_nat 8 0)) v_7497 (mux (eq v_7495 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7497 (mi (bitwidthMInt v_7497) -1))))) (concat (mux (sgt v_7505 (expression.bv_nat 8 0)) v_7507 (mux (eq v_7505 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7507 (mi (bitwidthMInt v_7507) -1))))) (concat (mux (sgt v_7515 (expression.bv_nat 8 0)) v_7517 (mux (eq v_7515 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7517 (mi (bitwidthMInt v_7517) -1))))) (concat (mux (sgt v_7525 (expression.bv_nat 8 0)) v_7527 (mux (eq v_7525 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7527 (mi (bitwidthMInt v_7527) -1))))) (concat (mux (sgt v_7535 (expression.bv_nat 8 0)) v_7537 (mux (eq v_7535 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7537 (mi (bitwidthMInt v_7537) -1))))) (concat (mux (sgt v_7545 (expression.bv_nat 8 0)) v_7547 (mux (eq v_7545 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7547 (mi (bitwidthMInt v_7547) -1))))) (concat (mux (sgt v_7555 (expression.bv_nat 8 0)) v_7557 (mux (eq v_7555 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7557 (mi (bitwidthMInt v_7557) -1))))) (concat (mux (sgt v_7565 (expression.bv_nat 8 0)) v_7567 (mux (eq v_7565 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7567 (mi (bitwidthMInt v_7567) -1))))) (mux (sgt v_7575 (expression.bv_nat 8 0)) v_7577 (mux (eq v_7575 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7577 (mi (bitwidthMInt v_7577) -1))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2927 : Mem) (v_2928 : reg (bv 128)) => do
      v_14635 <- evaluateAddress v_2927;
      v_14636 <- load v_14635 16;
      v_14637 <- eval (extract v_14636 0 8);
      v_14639 <- getRegister v_2928;
      v_14640 <- eval (extract v_14639 0 8);
      v_14648 <- eval (extract v_14636 8 16);
      v_14650 <- eval (extract v_14639 8 16);
      v_14658 <- eval (extract v_14636 16 24);
      v_14660 <- eval (extract v_14639 16 24);
      v_14668 <- eval (extract v_14636 24 32);
      v_14670 <- eval (extract v_14639 24 32);
      v_14678 <- eval (extract v_14636 32 40);
      v_14680 <- eval (extract v_14639 32 40);
      v_14688 <- eval (extract v_14636 40 48);
      v_14690 <- eval (extract v_14639 40 48);
      v_14698 <- eval (extract v_14636 48 56);
      v_14700 <- eval (extract v_14639 48 56);
      v_14708 <- eval (extract v_14636 56 64);
      v_14710 <- eval (extract v_14639 56 64);
      v_14718 <- eval (extract v_14636 64 72);
      v_14720 <- eval (extract v_14639 64 72);
      v_14728 <- eval (extract v_14636 72 80);
      v_14730 <- eval (extract v_14639 72 80);
      v_14738 <- eval (extract v_14636 80 88);
      v_14740 <- eval (extract v_14639 80 88);
      v_14748 <- eval (extract v_14636 88 96);
      v_14750 <- eval (extract v_14639 88 96);
      v_14758 <- eval (extract v_14636 96 104);
      v_14760 <- eval (extract v_14639 96 104);
      v_14768 <- eval (extract v_14636 104 112);
      v_14770 <- eval (extract v_14639 104 112);
      v_14778 <- eval (extract v_14636 112 120);
      v_14780 <- eval (extract v_14639 112 120);
      v_14788 <- eval (extract v_14636 120 128);
      v_14790 <- eval (extract v_14639 120 128);
      setRegister (lhs.of_reg v_2928) (concat (mux (sgt v_14637 (expression.bv_nat 8 0)) v_14640 (mux (eq v_14637 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14640 (mi (bitwidthMInt v_14640) -1))))) (concat (mux (sgt v_14648 (expression.bv_nat 8 0)) v_14650 (mux (eq v_14648 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14650 (mi (bitwidthMInt v_14650) -1))))) (concat (mux (sgt v_14658 (expression.bv_nat 8 0)) v_14660 (mux (eq v_14658 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14660 (mi (bitwidthMInt v_14660) -1))))) (concat (mux (sgt v_14668 (expression.bv_nat 8 0)) v_14670 (mux (eq v_14668 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14670 (mi (bitwidthMInt v_14670) -1))))) (concat (mux (sgt v_14678 (expression.bv_nat 8 0)) v_14680 (mux (eq v_14678 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14680 (mi (bitwidthMInt v_14680) -1))))) (concat (mux (sgt v_14688 (expression.bv_nat 8 0)) v_14690 (mux (eq v_14688 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14690 (mi (bitwidthMInt v_14690) -1))))) (concat (mux (sgt v_14698 (expression.bv_nat 8 0)) v_14700 (mux (eq v_14698 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14700 (mi (bitwidthMInt v_14700) -1))))) (concat (mux (sgt v_14708 (expression.bv_nat 8 0)) v_14710 (mux (eq v_14708 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14710 (mi (bitwidthMInt v_14710) -1))))) (concat (mux (sgt v_14718 (expression.bv_nat 8 0)) v_14720 (mux (eq v_14718 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14720 (mi (bitwidthMInt v_14720) -1))))) (concat (mux (sgt v_14728 (expression.bv_nat 8 0)) v_14730 (mux (eq v_14728 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14730 (mi (bitwidthMInt v_14730) -1))))) (concat (mux (sgt v_14738 (expression.bv_nat 8 0)) v_14740 (mux (eq v_14738 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14740 (mi (bitwidthMInt v_14740) -1))))) (concat (mux (sgt v_14748 (expression.bv_nat 8 0)) v_14750 (mux (eq v_14748 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14750 (mi (bitwidthMInt v_14750) -1))))) (concat (mux (sgt v_14758 (expression.bv_nat 8 0)) v_14760 (mux (eq v_14758 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14760 (mi (bitwidthMInt v_14760) -1))))) (concat (mux (sgt v_14768 (expression.bv_nat 8 0)) v_14770 (mux (eq v_14768 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14770 (mi (bitwidthMInt v_14770) -1))))) (concat (mux (sgt v_14778 (expression.bv_nat 8 0)) v_14780 (mux (eq v_14778 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14780 (mi (bitwidthMInt v_14780) -1))))) (mux (sgt v_14788 (expression.bv_nat 8 0)) v_14790 (mux (eq v_14788 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14790 (mi (bitwidthMInt v_14790) -1))))))))))))))))))));
      pure ()
    pat_end
