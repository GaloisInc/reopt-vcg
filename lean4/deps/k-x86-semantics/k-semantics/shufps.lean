def shufps1 : instruction :=
  definst "shufps" $ do
    pattern fun (v_3059 : imm int) (v_3061 : reg (bv 128)) (v_3062 : reg (bv 128)) => do
      v_6677 <- eval (handleImmediateWithSignExtend v_3059 8 8);
      v_6681 <- eval (eq (extract v_6677 0 1) (expression.bv_nat 1 1));
      v_6682 <- getRegister v_3061;
      v_6683 <- eval (extract v_6682 0 32);
      v_6684 <- eval (extract v_6682 64 96);
      v_6686 <- eval (extract v_6682 32 64);
      v_6687 <- eval (extract v_6682 96 128);
      v_6693 <- eval (eq (extract v_6677 2 3) (expression.bv_nat 1 1));
      v_6700 <- eval (eq (extract v_6677 4 5) (expression.bv_nat 1 1));
      v_6701 <- getRegister v_3062;
      v_6702 <- eval (extract v_6701 0 32);
      v_6703 <- eval (extract v_6701 64 96);
      v_6705 <- eval (extract v_6701 32 64);
      v_6706 <- eval (extract v_6701 96 128);
      v_6712 <- eval (eq (extract v_6677 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3062) (concat (mux (eq (extract v_6677 1 2) (expression.bv_nat 1 1)) (mux v_6681 v_6683 v_6684) (mux v_6681 v_6686 v_6687)) (concat (mux (eq (extract v_6677 3 4) (expression.bv_nat 1 1)) (mux v_6693 v_6683 v_6684) (mux v_6693 v_6686 v_6687)) (concat (mux (eq (extract v_6677 5 6) (expression.bv_nat 1 1)) (mux v_6700 v_6702 v_6703) (mux v_6700 v_6705 v_6706)) (mux (eq (extract v_6677 7 8) (expression.bv_nat 1 1)) (mux v_6712 v_6702 v_6703) (mux v_6712 v_6705 v_6706)))));
      pure ()
    pat_end;
    pattern fun (v_3054 : imm int) (v_3055 : Mem) (v_3056 : reg (bv 128)) => do
      v_10227 <- eval (handleImmediateWithSignExtend v_3054 8 8);
      v_10231 <- eval (eq (extract v_10227 0 1) (expression.bv_nat 1 1));
      v_10232 <- evaluateAddress v_3055;
      v_10233 <- load v_10232 16;
      v_10234 <- eval (extract v_10233 0 32);
      v_10235 <- eval (extract v_10233 64 96);
      v_10237 <- eval (extract v_10233 32 64);
      v_10238 <- eval (extract v_10233 96 128);
      v_10244 <- eval (eq (extract v_10227 2 3) (expression.bv_nat 1 1));
      v_10251 <- eval (eq (extract v_10227 4 5) (expression.bv_nat 1 1));
      v_10252 <- getRegister v_3056;
      v_10253 <- eval (extract v_10252 0 32);
      v_10254 <- eval (extract v_10252 64 96);
      v_10256 <- eval (extract v_10252 32 64);
      v_10257 <- eval (extract v_10252 96 128);
      v_10263 <- eval (eq (extract v_10227 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3056) (concat (mux (eq (extract v_10227 1 2) (expression.bv_nat 1 1)) (mux v_10231 v_10234 v_10235) (mux v_10231 v_10237 v_10238)) (concat (mux (eq (extract v_10227 3 4) (expression.bv_nat 1 1)) (mux v_10244 v_10234 v_10235) (mux v_10244 v_10237 v_10238)) (concat (mux (eq (extract v_10227 5 6) (expression.bv_nat 1 1)) (mux v_10251 v_10253 v_10254) (mux v_10251 v_10256 v_10257)) (mux (eq (extract v_10227 7 8) (expression.bv_nat 1 1)) (mux v_10263 v_10253 v_10254) (mux v_10263 v_10256 v_10257)))));
      pure ()
    pat_end
