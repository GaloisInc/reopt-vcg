def psrlw1 : instruction :=
  definst "psrlw" $ do
    pattern fun (v_3077 : imm int) (v_3078 : reg (bv 128)) => do
      v_7941 <- eval (handleImmediateWithSignExtend v_3077 8 8);
      v_7944 <- getRegister v_3078;
      v_7947 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_7941));
      setRegister (lhs.of_reg v_3078) (mux (ugt (concat (expression.bv_nat 56 0) v_7941) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_7944 0 16) v_7947) (concat (lshr (extract v_7944 16 32) v_7947) (concat (lshr (extract v_7944 32 48) v_7947) (concat (lshr (extract v_7944 48 64) v_7947) (concat (lshr (extract v_7944 64 80) v_7947) (concat (lshr (extract v_7944 80 96) v_7947) (concat (lshr (extract v_7944 96 112) v_7947) (lshr (extract v_7944 112 128) v_7947)))))))));
      pure ()
    pat_end;
    pattern fun (v_3086 : reg (bv 128)) (v_3087 : reg (bv 128)) => do
      v_7976 <- getRegister v_3086;
      v_7979 <- getRegister v_3087;
      v_7982 <- eval (uvalueMInt (extract v_7976 112 128));
      setRegister (lhs.of_reg v_3087) (mux (ugt (extract v_7976 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_7979 0 16) v_7982) (concat (lshr (extract v_7979 16 32) v_7982) (concat (lshr (extract v_7979 32 48) v_7982) (concat (lshr (extract v_7979 48 64) v_7982) (concat (lshr (extract v_7979 64 80) v_7982) (concat (lshr (extract v_7979 80 96) v_7982) (concat (lshr (extract v_7979 96 112) v_7982) (lshr (extract v_7979 112 128) v_7982)))))))));
      pure ()
    pat_end;
    pattern fun (v_3082 : Mem) (v_3083 : reg (bv 128)) => do
      v_14597 <- evaluateAddress v_3082;
      v_14598 <- load v_14597 16;
      v_14601 <- getRegister v_3083;
      v_14604 <- eval (uvalueMInt (extract v_14598 112 128));
      setRegister (lhs.of_reg v_3083) (mux (ugt (extract v_14598 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_14601 0 16) v_14604) (concat (lshr (extract v_14601 16 32) v_14604) (concat (lshr (extract v_14601 32 48) v_14604) (concat (lshr (extract v_14601 48 64) v_14604) (concat (lshr (extract v_14601 64 80) v_14604) (concat (lshr (extract v_14601 80 96) v_14604) (concat (lshr (extract v_14601 96 112) v_14604) (lshr (extract v_14601 112 128) v_14604)))))))));
      pure ()
    pat_end
