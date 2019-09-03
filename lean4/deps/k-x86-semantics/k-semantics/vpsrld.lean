def vpsrld1 : instruction :=
  definst "vpsrld" $ do
    pattern fun (v_3293 : imm int) (v_3295 : reg (bv 128)) (v_3296 : reg (bv 128)) => do
      v_8743 <- eval (handleImmediateWithSignExtend v_3293 8 8);
      v_8746 <- getRegister v_3295;
      v_8749 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_8743));
      setRegister (lhs.of_reg v_3296) (mux (ugt (concat (expression.bv_nat 56 0) v_8743) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8746 0 32) v_8749) (concat (lshr (extract v_8746 32 64) v_8749) (concat (lshr (extract v_8746 64 96) v_8749) (lshr (extract v_8746 96 128) v_8749)))));
      pure ()
    pat_end;
    pattern fun (v_3305 : reg (bv 128)) (v_3306 : reg (bv 128)) (v_3307 : reg (bv 128)) => do
      v_8767 <- getRegister v_3305;
      v_8770 <- getRegister v_3306;
      v_8773 <- eval (uvalueMInt (extract v_8767 96 128));
      setRegister (lhs.of_reg v_3307) (mux (ugt (extract v_8767 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8770 0 32) v_8773) (concat (lshr (extract v_8770 32 64) v_8773) (concat (lshr (extract v_8770 64 96) v_8773) (lshr (extract v_8770 96 128) v_8773)))));
      pure ()
    pat_end;
    pattern fun (v_3310 : imm int) (v_3313 : reg (bv 256)) (v_3314 : reg (bv 256)) => do
      v_8786 <- eval (handleImmediateWithSignExtend v_3310 8 8);
      v_8789 <- getRegister v_3313;
      v_8792 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_8786));
      setRegister (lhs.of_reg v_3314) (mux (ugt (concat (expression.bv_nat 56 0) v_8786) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_8789 0 32) v_8792) (concat (lshr (extract v_8789 32 64) v_8792) (concat (lshr (extract v_8789 64 96) v_8792) (concat (lshr (extract v_8789 96 128) v_8792) (concat (lshr (extract v_8789 128 160) v_8792) (concat (lshr (extract v_8789 160 192) v_8792) (concat (lshr (extract v_8789 192 224) v_8792) (lshr (extract v_8789 224 256) v_8792)))))))));
      pure ()
    pat_end;
    pattern fun (v_3322 : reg (bv 128)) (v_3324 : reg (bv 256)) (v_3325 : reg (bv 256)) => do
      v_8822 <- getRegister v_3322;
      v_8825 <- getRegister v_3324;
      v_8828 <- eval (uvalueMInt (extract v_8822 96 128));
      setRegister (lhs.of_reg v_3325) (mux (ugt (extract v_8822 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_8825 0 32) v_8828) (concat (lshr (extract v_8825 32 64) v_8828) (concat (lshr (extract v_8825 64 96) v_8828) (concat (lshr (extract v_8825 96 128) v_8828) (concat (lshr (extract v_8825 128 160) v_8828) (concat (lshr (extract v_8825 160 192) v_8828) (concat (lshr (extract v_8825 192 224) v_8828) (lshr (extract v_8825 224 256) v_8828)))))))));
      pure ()
    pat_end;
    pattern fun (v_3299 : Mem) (v_3300 : reg (bv 128)) (v_3301 : reg (bv 128)) => do
      v_14769 <- evaluateAddress v_3299;
      v_14770 <- load v_14769 16;
      v_14773 <- getRegister v_3300;
      v_14776 <- eval (uvalueMInt (extract v_14770 96 128));
      setRegister (lhs.of_reg v_3301) (mux (ugt (extract v_14770 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_14773 0 32) v_14776) (concat (lshr (extract v_14773 32 64) v_14776) (concat (lshr (extract v_14773 64 96) v_14776) (lshr (extract v_14773 96 128) v_14776)))));
      pure ()
    pat_end;
    pattern fun (v_3316 : Mem) (v_3318 : reg (bv 256)) (v_3319 : reg (bv 256)) => do
      v_14789 <- evaluateAddress v_3316;
      v_14790 <- load v_14789 16;
      v_14793 <- getRegister v_3318;
      v_14796 <- eval (uvalueMInt (extract v_14790 96 128));
      setRegister (lhs.of_reg v_3319) (mux (ugt (extract v_14790 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_14793 0 32) v_14796) (concat (lshr (extract v_14793 32 64) v_14796) (concat (lshr (extract v_14793 64 96) v_14796) (concat (lshr (extract v_14793 96 128) v_14796) (concat (lshr (extract v_14793 128 160) v_14796) (concat (lshr (extract v_14793 160 192) v_14796) (concat (lshr (extract v_14793 192 224) v_14796) (lshr (extract v_14793 224 256) v_14796)))))))));
      pure ()
    pat_end
