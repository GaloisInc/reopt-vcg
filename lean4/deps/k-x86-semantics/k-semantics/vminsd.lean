def vminsd1 : instruction :=
  definst "vminsd" $ do
    pattern fun (v_2712 : reg (bv 128)) (v_2713 : reg (bv 128)) (v_2714 : reg (bv 128)) => do
      v_4678 <- getRegister v_2713;
      v_4680 <- eval (extract v_4678 64 128);
      v_4681 <- getRegister v_2712;
      v_4682 <- eval (extract v_4681 64 128);
      setRegister (lhs.of_reg v_2714) (concat (extract v_4678 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4680 v_4682) (expression.bv_nat 1 1)) v_4680 v_4682));
      pure ()
    pat_end;
    pattern fun (v_2707 : Mem) (v_2708 : reg (bv 128)) (v_2709 : reg (bv 128)) => do
      v_10104 <- getRegister v_2708;
      v_10106 <- eval (extract v_10104 64 128);
      v_10107 <- evaluateAddress v_2707;
      v_10108 <- load v_10107 8;
      setRegister (lhs.of_reg v_2709) (concat (extract v_10104 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10106 v_10108) (expression.bv_nat 1 1)) v_10106 v_10108));
      pure ()
    pat_end
