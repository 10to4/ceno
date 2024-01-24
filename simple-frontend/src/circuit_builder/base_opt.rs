use ff::Field;
use goldilocks::SmallField;

use crate::structs::{
    Cell, CellId, CellType, CircuitBuilder, ConstantType, GateType, InType, MixedCell, OutType,
    WireId,
};

impl<F: SmallField> CircuitBuilder<F> {
    pub fn create_cell(&mut self) -> CellId {
        self.cells.push(Cell::new());
        self.cells.len() - 1
    }

    pub fn create_cells(&mut self, num: usize) -> Vec<CellId> {
        self.cells.extend((0..num).map(|_| Cell::new()));
        (self.cells.len() - num..self.cells.len()).collect()
    }

    /// This is to mark the cells with special functionality.
    pub(crate) fn mark_cells(&mut self, cell_type: CellType, cells: &[CellId]) {
        cells.iter().for_each(|cell| {
            self.cells[*cell].cell_type = Some(cell_type);
        });
    }

    pub fn create_wire_in(&mut self, num: usize) -> (WireId, Vec<CellId>) {
        let cell = self.create_cells(num);
        self.mark_cells(CellType::In(InType::Wire(self.n_wires_in as WireId)), &cell);
        self.n_wires_in += 1;
        ((self.n_wires_in - 1) as WireId, cell)
    }

    /// Create input cells and assign it to be constant.
    pub fn create_constant_in(&mut self, num: usize, constant: i64) -> Vec<CellId> {
        let cell = self.create_cells(num);
        self.mark_cells(CellType::In(InType::Constant(constant)), &cell);
        cell
    }

    /// Create input cells as a counter. It should count from 0 to n_instance *
    /// num through the whole circuit.
    pub fn create_counter_in(&mut self, num_vars: usize) -> Vec<CellId> {
        let cell = self.create_cells(1 << num_vars);
        self.mark_cells(CellType::In(InType::Counter(num_vars)), &cell);
        cell
    }

    pub fn create_wire_out(&mut self, num: usize) -> (WireId, Vec<CellId>) {
        let cell = self.create_cells(num);
        self.mark_cells(
            CellType::Out(OutType::Wire(self.n_wires_out as WireId)),
            &cell,
        );
        self.n_wires_out += 1;
        ((self.n_wires_out - 1) as WireId, cell)
    }

    pub fn create_wire_out_from_cells(&mut self, cells: &[CellId]) -> WireId {
        self.mark_cells(
            CellType::Out(OutType::Wire(self.n_wires_out as WireId)),
            &cells,
        );
        self.n_wires_out += 1;
        (self.n_wires_out - 1) as WireId
    }

    pub fn add_const(&mut self, out: CellId, constant: F::BaseField) {
        if constant == F::BaseField::ZERO {
            return;
        }
        self.add_const_internal(out, ConstantType::Field(constant));
    }

    pub(crate) fn add_const_internal(&mut self, out: CellId, constant: ConstantType<F>) {
        let out_cell = &mut self.cells[out];
        out_cell.gates.push(GateType::AddC(constant));
    }

    pub fn add(&mut self, out: CellId, in_0: CellId, scalar: F::BaseField) {
        if scalar == F::BaseField::ZERO {
            return;
        }
        self.add_internal(out, in_0, ConstantType::Field(scalar));
    }

    pub(crate) fn add_internal(&mut self, out: CellId, in_0: CellId, scalar: ConstantType<F>) {
        let out_cell = &mut self.cells[out];
        out_cell.gates.push(GateType::Add(in_0, scalar));
    }

    pub fn mul2(&mut self, out: CellId, in_0: CellId, in_1: CellId, scalar: F::BaseField) {
        if scalar == F::BaseField::ZERO {
            return;
        }
        self.mul2_internal(out, in_0, in_1, ConstantType::Field(scalar));
    }

    pub(crate) fn mul2_internal(
        &mut self,
        out: CellId,
        in_0: CellId,
        in_1: CellId,
        scalar: ConstantType<F>,
    ) {
        let out_cell = &mut self.cells[out];
        out_cell.gates.push(GateType::Mul2(in_0, in_1, scalar));
    }

    pub fn mul3(
        &mut self,
        out: CellId,
        in_0: CellId,
        in_1: CellId,
        in_2: CellId,
        scalar: F::BaseField,
    ) {
        if scalar == F::BaseField::ZERO {
            return;
        }
        self.mul3_internal(out, in_0, in_1, in_2, ConstantType::Field(scalar));
    }

    pub(crate) fn mul3_internal(
        &mut self,
        out: CellId,
        in_0: CellId,
        in_1: CellId,
        in_2: CellId,
        scalar: ConstantType<F>,
    ) {
        let out_cell = &mut self.cells[out];
        out_cell
            .gates
            .push(GateType::Mul3(in_0, in_1, in_2, scalar));
    }

    pub fn assert_const(&mut self, out: CellId, constant: F::BaseField) {
        let out_cell = &mut self.cells[out];
        out_cell.assert_const = Some(constant);
    }

    pub fn add_cell_expr(&mut self, out: CellId, in_0: MixedCell<F>) {
        match in_0 {
            MixedCell::Constant(constant) => {
                self.add_const(out, constant);
            }
            MixedCell::Cell(cell_id) => {
                self.add(out, cell_id, F::BaseField::ONE);
            }
            MixedCell::CellExpr(cell_id, a, b) => {
                self.add(out, cell_id, a);
                self.add_const(out, b);
            }
        };
    }

    pub fn sel(&mut self, out: CellId, in_0: CellId, in_1: CellId, cond: CellId) {
        // (1 - cond) * in_0 + cond * in_1 = (in_1 - in_0) * cond + in_0
        let diff = self.create_cell();
        self.add(diff, in_1, F::BaseField::ONE);
        self.add(diff, in_0, -F::BaseField::ONE);
        self.mul2(out, diff, cond, F::BaseField::ONE);
        self.add(out, in_0, F::BaseField::ONE);
    }

    pub fn sel_mixed(&mut self, out: CellId, in_0: MixedCell<F>, in_1: MixedCell<F>, cond: CellId) {
        // (1 - cond) * in_0 + cond * in_1 = (in_1 - in_0) * cond + in_0
        match (in_0, in_1) {
            (MixedCell::Constant(in_0), MixedCell::Constant(in_1)) => {
                self.add(out, cond, in_1 - in_0);
            }
            (MixedCell::Constant(in_0), in_1) => {
                let diff = in_1.expr(F::BaseField::ONE, -in_0);
                let diff_cell = self.create_cell();
                self.add_cell_expr(diff_cell, diff);
                self.mul2(out, diff_cell, cond, F::BaseField::ONE);
                self.add_const(out, in_0);
            }
            (in_0, MixedCell::Constant(in_1)) => {
                self.add_cell_expr(out, in_0);
                let diff = in_0.expr(-F::BaseField::ONE, in_1);
                let diff_cell = self.create_cell();
                self.add_cell_expr(diff_cell, diff);
                self.mul2(out, diff_cell, cond, F::BaseField::ONE);
            }
            (in_0, in_1) => {
                self.add_cell_expr(out, in_0);
                let diff = self.create_cell();
                self.add_cell_expr(diff, in_1);
                self.add_cell_expr(diff, in_0.expr(-F::BaseField::ONE, F::BaseField::ZERO));
                self.mul2(out, diff, cond, F::BaseField::ONE);
            }
        }
    }
}