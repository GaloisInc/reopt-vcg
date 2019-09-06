def minss1 : instruction :=
  definst "minss" $ do
    pattern fun (v_3205 : reg (bv 128)) (v_3206 : reg (bv 128)) => do
      v_5715 <- getRegister v_3206;
      v_5717 <- eval (extract v_5715 96 128);
      v_5718 <- getRegister v_3205;
      v_5719 <- eval (extract v_5718 96 128);
      setRegister (lhs.of_reg v_3206) (concat (extract v_5715 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5717 v_5719) (expression.bv_nat 1 1)) v_5717 v_5719));
      pure ()
    pat_end;
    pattern fun (v_3201 : Mem) (v_3202 : reg (bv 128)) => do
      v_8946 <- getRegister v_3202;
      v_8948 <- eval (extract v_8946 96 128);
      v_8949 <- evaluateAddress v_3201;
      v_8950 <- load v_8949 4;
      setRegister (lhs.of_reg v_3202) (concat (extract v_8946 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8948 v_8950) (expression.bv_nat 1 1)) v_8948 v_8950));
      pure ()
    pat_end
